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
(include-book "docgen")
(include-book "fixequiv")
(include-book "fty-sum")
(include-book "fty-alist")
(include-book "fty-list")
(include-book "fty-transsum")
(include-book "kestrel/fty/fty-set" :dir :system)
(include-book "fty-sugar")
(include-book "std/util/deflist-base" :dir :system)
(include-book "std/util/defalist-base" :dir :system)
(include-book "std/lists/acl2-count" :dir :system)
(set-state-ok t)

(set-compile-fns t) ; avoid possible GCL stack overflow

;; Lemmas for deftagprod.
(defthmd equal-of-strip-cars
  (implies (syntaxp (quotep y))
           (equal (equal (strip-cars x) y)
                  (if (atom y)
                      (and (not y) (atom x))
                    (and (consp x)
                         (equal (strip-cars (cdr x)) (cdr y))
                         (if (car y)
                             (and (consp (car x))
                                  (equal (caar x) (car y)))
                           (or (atom (car x))
                               (equal (caar x) nil))))))))

;; seems generally good so we'll leave it enabled
(defthm strip-cars-under-iff
  (iff (strip-cars x) (consp x)))

(defthmd equal-of-plus-one
  (implies (syntaxp (quotep y))
           (equal (equal (+ 1 x) y)
                  (and (acl2-numberp y)
                       (equal (fix x) (+ -1 y))))))

(defthmd consp-when-tag
  (implies (tag x)
           (consp x))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthmd len-of-cons
  (equal (len (cons a b))
         (+ 1 (len b))))

(defthmd equal-of-len
  (implies (syntaxp (quotep n))
           (equal (equal (len x) n)
                  (if (zp n)
                      (and (equal n 0) (not (consp x)))
                    (and (consp x)
                         (equal (len (cdr x)) (+ -1 n)))))))

(defthmd open-member-equal-on-list-of-tags
  ;; This especially helps with certain transsum kind/fix theorems.
  (implies (syntaxp (and (quotep val)
                         (symbol-listp (unquote val))))
           (equal (member-equal a val)
                  (cond ((atom val) nil)
                        ((equal a (car val)) val)
                        (t (member-equal a (cdr val))))))
  :hints(("Goal" :in-theory (enable member-equal))))

(defthmd alistp-compound-recognizer
  (implies (alistp x)
           (true-listp x))
  :rule-classes :compound-recognizer)

(deftheory deftypes-theory
  '(equal-of-strip-cars
    car-cons cdr-cons
    strip-cars
    strip-cars-under-iff
    eqlablep (len) len-of-cons
    equal-of-len (zp)
    (:t acl2-count)
    acl2::acl2-count-of-car
    acl2::acl2-count-of-cdr
    acl2::acl2-count-of-consp-positive
    acl2::acl2-count-of-cons-greater
    o< o-finp
    (natp) acl2::natp-compound-recognizer
    hons
    open-member-equal-on-list-of-tags
    alistp-compound-recognizer
    ;;  len
    ;; equal-of-plus-one fix
    prod-car
    prod-cdr
    prod-hons
    std::cons-with-hint
    std::prod-cons-with-hint
    std::car-of-prod-cons
    std::cdr-of-prod-cons
    std::prod-cons-of-car/cdr
    std::acl2-count-of-prod-cons
    std::prod-cons-equal-cons
    std::prod-cons-when-either
    std::prod-consp-compound-recognizer
    std::prod-cons-not-consp-forward))


(program)


;; ------------------------- Deftypes Parsing -----------------------

(defun parse-flextypelist (x xvar our-fixtypes fixtypes state)
  (if (atom x)
      nil
    (cons (case (caar x)
            (defflexsum  (parse-flexsum (cdar x) xvar our-fixtypes fixtypes))
            (defprod     (parse-defprod (cdar x) xvar our-fixtypes fixtypes))
            (deftagsum   (parse-tagsum (cdar x) xvar our-fixtypes fixtypes))
            (defoption   (parse-option (cdar x) xvar our-fixtypes fixtypes))
            (deftranssum (parse-transsum (cdar x) xvar our-fixtypes fixtypes state))
            (deflist     (parse-flexlist (cdar x) xvar our-fixtypes fixtypes state))
            (defalist    (parse-flexalist (cdar x) xvar our-fixtypes fixtypes state))
            (defmap      (let ((al (parse-flexalist (cdar x) xvar
                                                    our-fixtypes fixtypes state)))
                           (change-flexalist al :strategy :drop-keys)))
            (defset      (parse-flexset (cdar x) xvar our-fixtypes fixtypes state))
            (otherwise (er hard? 'parse-flextypelist
                           "Recognized flextypes are ~x0, not ~x1~%"
                           *known-flextype-generators* (caar x))))
          (parse-flextypelist (cdr x) xvar our-fixtypes fixtypes state))))



(defconst *flextypes-keywords*
  '(:xvar
    :no-count
    :parents
    :short
    :long
    :prepwork
    :post-pred-events
    :post-fix-events
    :post-events
    :enable-rules
    :verbosep))


(defun parse-flextypes (x state)
  (b* (((cons name x) x)
       ((unless (symbolp name))
        (er hard? 'parse-flextypes
            "Malformed flextypes: name must be a symbol, but found ~x0" name))
       ((mv pre-/// post-///) (std::split-/// 'parse-flexsum x))
       ((mv kwd-alist typedecls)
        (extract-keywords 'parse-flextypes *flextypes-keywords* pre-/// nil))
       (our-fixtypes (flextype-forms->fixtypes typedecls))
       (fixtype-al (append our-fixtypes
                           (get-fixtypes-alist (w state))))
       (xvar (getarg :xvar nil kwd-alist))
       (no-count (getarg :no-count nil kwd-alist))
       (types (parse-flextypelist typedecls xvar our-fixtypes fixtype-al state)))
    (make-flextypes :name name
                    :types types
                    :no-count no-count
                    :kwd-alist (if post-///
                                   (cons (cons :///-events post-///)
                                         kwd-alist)
                                 kwd-alist)
                    :recp (flextypelist-recp types))))

(defun flextypelist-predicate-defs (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types))
            (flex*-predicate-def x))
          (flextypelist-predicate-defs (cdr types)))))

(defun flextypes-predicate-def (x)
  (b* (((flextypes x) x)
       (defs (flextypelist-predicate-defs x.types)))
    (if (atom (cdr x.types))
        `(,(car defs)
          (local (in-theory (disable . ,(flextypelist-predicates x.types)))))
      `((defines ,(intern-in-package-of-symbol (cat (symbol-name x.name) "-P")
                                               x.name)
          :progn t
          ,@defs)
        (local (in-theory (disable . ,(flextypelist-predicates x.types))))))))

(defun flextypelist-fix-defs (types flagp)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types))
            (flex*-fix-def x flagp))
          (flextypelist-fix-defs (cdr types) flagp))))

(defun flextypelist-fix-postevents (types)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types))
              (flex*-fix-postevents x))
            (flextypelist-fix-postevents (cdr types)))))


;; ------------------ Fix-when-predicate theorem -----------------------

(defun flextypelist-fix-when-pred-thms (types flagp)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types))
            (flex*-fix-when-pred-thm x flagp))
          (flextypelist-fix-when-pred-thms (cdr types) flagp))))

(defun flextypelist-pred-calls (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types))
            (list x.pred x.xvar))
          (flextypelist-pred-calls (cdr types)))))

(defun flextypelist-fixtypes (types)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types))
              `((defsection ,x.equiv
                  :parents (,x.name)
                  :short ,(cat "Basic equivalence relation for " (xdoc::see x.name) " structures.")
                  (deffixtype ,x.name
                    :pred ,x.pred
                    :fix ,x.fix
                    :equiv ,x.equiv
                    :define t :forward t))
                (local (in-theory (enable ,x.equiv)))))
            (flextypelist-fixtypes (cdr types)))))

(defun flextypes-form-append-hints (new-hints form)
  (b* ((mem (member :hints form))
       ((unless mem) (append form `(:hints ,new-hints)))
       (prefix (take (- (len form) (len mem)) form)))
    (append prefix (cons :hints (cons (append new-hints (cadr mem))
                                      (cddr mem))))))

(defun flextypes-collect-sum-kind-calls (types)
  (if (atom types)
      nil
    (append (case (tag (car types))
              (:sum (b* (((flexsum sum) (car types)))
                          (if sum.kind
                              (list `(,sum.kind ,sum.xvar))
                            nil)))
              (otherwise nil))
            (flextypes-collect-sum-kind-calls (cdr types)))))

(defun flextypes-fix-def (x)
  (b* (((flextypes x) x)
       (flagp (consp (cdr x.types)))
       (defs (flextypelist-fix-defs x.types flagp))
       (flag-name (and flagp
                       (intern-in-package-of-symbol (cat (symbol-name x.name) "-FIX-FLAG")
                                                    x.name)))
       (flag-defthm-name (and flagp
                              (flag::thm-macro-name flag-name)))
       (fix-when-pred-thms
        (flextypelist-fix-when-pred-thms x.types flagp))
       (sum-kind-calls (flextypes-collect-sum-kind-calls x.types)))
    `(,(append (if flagp
                   `(defines ,(intern-in-package-of-symbol (cat (symbol-name x.name) "-FIX")
                                                           x.name)
                      :flag ,flag-name
                      :bogus-ok t       ; Allows non-recursive fix function (e.g. for defset)
                      :progn t
                      ,@(and sum-kind-calls
                             `(:hints ((and stable-under-simplificationp
                                            '(:expand ,sum-kind-calls)))))
                      ,@defs
                      ///)
                 (car defs))
               `(
                 (local (in-theory (disable . ,(pairlis$
                                                (make-list (len x.types) :initial-element :d)
                                                (pairlis$ (flextypelist-fixes x.types) nil)))))
                 ,(if flagp
                      `(,flag-defthm-name . ,fix-when-pred-thms)
                    (if x.recp
                        (flextypes-form-append-hints
                         '(("goal" :induct t))
                         (car fix-when-pred-thms))
                      (car fix-when-pred-thms)))

                 (verify-guards+ ,(with-flextype-bindings (x (car x.types)) x.fix)
                   :hints (("goal"
                            :expand (,@(append (flextypelist-pred-calls x.types)
                                               sum-kind-calls)))))

                 ,@(flextypelist-fixtypes x.types)

                 . ,(flextypelist-fix-postevents x.types)))
      (local (in-theory (enable . ,(flextypelist-equivs x.types))))
      (local (in-theory (disable . ,(flextypelist-fixes x.types))))
      )))






(defun flextypes-fns (types)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types)) (flex*-fns x))
            (flextypes-fns (cdr types)))))

(defun flextypes-acc/ctors (types)
  (if (atom types)
      nil
    (append (and (eq (caar types) :sum)
                 (flexsum-prod-fns (flexsum->prods (car types))))
            (flextypes-acc/ctors (cdr types)))))

(defun flextypes-ctors (types)
  (if (atom types)
      nil
    (append (and (eq (caar types) :sum)
                 (flexsum-prod-ctors (flexsum->prods (car types))))
            (flextypes-ctors (cdr types)))))


;; ------------------ Count events: deftypes -----------------------
(defun flextypes-count-defs (x alltypes)
  (if (atom x)
      nil
    (append (with-flextype-bindings (x (car x))
              (flex*-count x alltypes))
            (flextypes-count-defs (cdr x) alltypes))))

(defun flextypes-count-expands (types)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types))
              (and x.count
                   `((,x.count ,x.xvar)
                     (,x.count (,x.fix ,x.xvar)))))
            (flextypes-count-expands (cdr types)))))

(defun flextypes-count-names (x)
  (if (atom x)
      nil
    (append (with-flextype-bindings (x (car x))
              (and x.count (list x.count)))
            (flextypes-count-names (cdr x)))))

(defun flextypes-count-post-events (types alltypes)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types))
              (flex*-count-post-events x alltypes))
            (flextypes-count-post-events (cdr types) alltypes))))

(defun flextypes-nokind-expand-fixes (types)
  (if (atom types)
      nil
    (if (and (eq (tag (car types)) :sum)
             (not (flexsum->kind (car types))))
        (cons `(,(flexsum->fix (car types)) ,(flexsum->xvar (car types)))
              (flextypes-nokind-expand-fixes (cdr types)))
      (flextypes-nokind-expand-fixes (cdr types)))))

(defun flextypes-expand-fixes (types)
  (if (atom types)
      nil
    (cons (with-flextype-bindings (x (car types))
            `(,x.fix ,x.xvar))
          (flextypes-expand-fixes (cdr types)))))

(defun flexprods-ctor-of-fields-thms (prods)
  (b* (((when (atom prods))
        nil)
       ((unless (consp (flexprod->fields (car prods))))
        (flexprods-ctor-of-fields-thms (cdr prods)))
       (foo-of-fields (intern-in-package-of-symbol
                       (cat (symbol-name (flexprod->ctor-name (car prods))) "-OF-FIELDS")
                       (flexprod->ctor-name (car prods)))))
    (cons foo-of-fields
          (flexprods-ctor-of-fields-thms (cdr prods)))))

(defun flextypes-ctor-of-fields-thms (types)
  (if (atom types)
      nil
    (append (and (eq (caar types) :sum)
                 (flexprods-ctor-of-fields-thms (flexsum->prods (car types))))
            (flextypes-ctor-of-fields-thms (cdr types)))))

(defun flexprods-fix-when-kind-thms (prods sum)
  (b* (((when (atom prods))
        nil)
       ((unless (consp (flexprod->fields (car prods))))
        (flexprods-fix-when-kind-thms (cdr prods) sum))
       (foo-fix-when-subfoo-kind (intern-in-package-of-symbol
                                  (cat (symbol-name (flexsum->fix sum)) "-WHEN-"
                                       (symbol-name (flexprod->kind (car prods))))
                                  (flexsum->fix sum))))
    (cons foo-fix-when-subfoo-kind
          (flexprods-fix-when-kind-thms (cdr prods) sum))))

(defun flextypes-fix-when-kind-thms (types)
  (if (atom types)
      nil
    (append (and (eq (caar types) :sum)
                 (consp (cdr (flexsum->prods (car types))))
                 (flexprods-fix-when-kind-thms (flexsum->prods (car types)) (car types)))
            (flextypes-fix-when-kind-thms (cdr types)))))

(defun flextypes-count (x)
  (b* (((flextypes x) x)
       ((when x.no-count) nil)
       (defs (flextypes-count-defs x.types x.types))
       (names (flextypes-count-names x.types))
       ((when (not defs)) ;; none of the types have a count
        nil)
       (flagp (consp (cdr defs)))
       (measure-hints
        ;; original
        ;; `((and stable-under-simplificationp
        ;;        '(:in-theory (enable . ,(flextypes-acc/ctors x.types))))
        ;;   (and stable-under-simplificationp
        ;;        '(:expand ,(flextypes-nokind-expand-fixes x.types))))
        `((and stable-under-simplificationp
               '(:expand ,(flextypes-expand-fixes x.types)
                 :in-theory (e/d  ,(flextypes-ctors x.types))
                 )))
        )
       (prepwork `((local (in-theory (e/d ,(flextypes-fix-when-kind-thms x.types)
                                          ,(flextypes-ctor-of-fields-thms x.types)))))))
    (if flagp
        (let ((defines-name (intern-in-package-of-symbol (cat (symbol-name x.name) "-COUNT")
                                                         x.name)))
          `((defines ,defines-name
              :hints ,measure-hints
              :prepwork ,prepwork
              :progn t
              ,@defs
              ///
              (local (in-theory (disable . ,(flextypes-count-names x.types))))
              (verify-guards+ ,(cadr (car defs)))
              (deffixequiv-mutual ,defines-name
                :hints (;; ("goal" :expand ,(flextypes-count-expands x.types))
                        (and stable-under-simplificationp
                             (let ((lit (car (last clause))))
                               (and (eq (car lit) 'equal)
                                    (let ((expands (append (and (consp (cadr lit))
                                                                (member (car (cadr lit))
                                                                        ',names)
                                                                (list (cadr lit)))
                                                           (and (consp (caddr lit))
                                                                (member (car (caddr lit))
                                                                        ',names)
                                                                (list (caddr lit))))))
                                      (and expands
                                           `(:expand ,expands))))))))

              . ,(flextypes-count-post-events x.types x.types))))
      (list
       (append
        (car defs)
        `(:hints ,measure-hints
          :prepwork ,prepwork
          ///
          (local (in-theory (disable . ,(flextypes-count-names x.types))))
          (verify-guards+ ,(cadr (car defs))
                          :hints ((and stable-under-simplificationp
                                       '(:expand ,(flextypes-nokind-expand-fixes x.types)))))
          (deffixequiv ,(cadr (car defs))
            :hints (("goal" :expand ,(flextypes-count-expands x.types))
                    (and stable-under-simplificationp
                         '(:expand ,(flextypes-nokind-expand-fixes x.types)))))
          . ,(flextypes-count-post-events x.types x.types)))))))


;; ------------------ Ambient Theory Managment -----------------------
(defun find-fix-when-pred-thm-aux (fix pred fix-rules)
  (if (atom fix-rules)
      (let ((body `(implies (,pred x)
                            (equal (,fix x) x))))
        (mv nil `(local (make-event
                         '(:or (defthm ,(intern-in-package-of-symbol
                                         (cat "TMP-DEFTYPES-" (symbol-name fix) "-WHEN-" (symbol-name pred))
                                         'fty)
                                 ,body)
                           (value-triple
                            (er hard? 'deftypes
                                "To use ~x0/~x1 as a fixing function/predicate, we must ~
                       be able to prove the following: ~x2.  But this proof ~
                       failed! Please try to prove this rule yourself."
                                ',fix ',pred ',body)))))))
    (let ((rune (b* ((rule (car fix-rules))
                     (subclass (acl2::access acl2::rewrite-rule rule :subclass))
                     ((unless (eq subclass 'acl2::backchain)) nil)
                     (lhs (acl2::access acl2::rewrite-rule rule :lhs))
                     ((unless (symbolp (cadr lhs))) nil)
                     (var (cadr lhs))
                     (rhs (acl2::access acl2::rewrite-rule rule :rhs))
                     ((unless (eq rhs var)) nil)
                     (hyps (acl2::access acl2::rewrite-rule rule :hyps))
                     ((unless (and (consp hyps)
                                   (not (cdr hyps))
                                   (consp (car hyps))
                                   (eq pred (caar hyps))
                                   (eq var (cadr (car hyps)))))
                      nil)
                     (equiv (acl2::access acl2::rewrite-rule rule :equiv))
                     ((unless (eq equiv 'equal)) nil)
                     ((unless (eq (acl2::access acl2::rewrite-rule rule :backchain-limit-lst) nil)) nil))
                  (acl2::access acl2::rewrite-rule rule :rune))))
      (if rune
          (mv t rune)
        (find-fix-when-pred-thm-aux fix pred (cdr fix-rules))))))

(defun find-fix-when-unsigned-byte-p-pred-thm-aux (fix pred size fix-rules)
  (if (atom fix-rules)
      (let ((body `(implies (acl2::unsigned-byte-p (acl2::quote ,size) x)
                            (equal (,fix x) x))))
        (mv nil `(local (make-event
                         '(:or (defthm ,(intern-in-package-of-symbol
                                         (cat "TMP-DEFTYPES-" (symbol-name fix) "-WHEN-" (symbol-name pred))
                                         'fty)
                                 ,body)
                           (value-triple
                            (er hard? 'deftypes
                                "To use ~x0/~x1 as a fixing function/predicate, we must ~
                       be able to prove the following: ~x2.  But this proof ~
                       failed! Please try to prove this rule yourself."
                                ',fix ',pred ',body)))))))
    (let ((rune (b* ((rule (car fix-rules))
                     (subclass (acl2::access acl2::rewrite-rule rule :subclass))
                     ((unless (eq subclass 'acl2::backchain)) nil)
                     (lhs (acl2::access acl2::rewrite-rule rule :lhs))
                     ((unless (symbolp (cadr lhs))) nil)
                     (var (cadr lhs))
                     (rhs (acl2::access acl2::rewrite-rule rule :rhs))
                     ((unless (eq rhs var)) nil)
                     (hyps (acl2::access acl2::rewrite-rule rule :hyps))
                     ((unless (and (consp hyps)
                                   (not (cdr hyps))
                                   (consp (car hyps))
                                   (eq 'acl2::unsigned-byte-p (caar hyps))
                                   (consp (cadar hyps))
                                   (equal 'acl2::quote (car (cadar hyps)))
                                   (eq size (cadr (cadar hyps)))
                                   (eq var (caddr (car hyps)))))
                      nil)
                     (equiv (acl2::access acl2::rewrite-rule rule :equiv))
                     ((unless (eq equiv 'equal)) nil)
                     ((unless (eq (acl2::access acl2::rewrite-rule rule :backchain-limit-lst) nil)) nil))
                  (acl2::access acl2::rewrite-rule rule :rune))))
      (if rune
          (mv t rune)
        (find-fix-when-unsigned-byte-p-pred-thm-aux fix pred size (cdr fix-rules))))))

(defun find-pred-of-fix-thm-aux (fix pred pred-rules)
  (if (atom pred-rules)
      (let ((body `(,pred (,fix x))))
        (mv nil
            `(local (make-event
                     '(:or (defthm ,(intern-in-package-of-symbol
                                     (cat "TMP-DEFTYPES-" (symbol-name PRED) "-OF-" (symbol-name fix))
                                     'fty)
                             ,body)
                       (value-triple
                        (er hard? 'deftypes
                            "To use ~x0/~x1 as a fixing function/predicate, we must ~
                       be able to prove the following: ~x2.  But this proof ~
                       failed! Please try to prove this rule yourself."
                            ',fix ',pred ',body)))))))
    (let ((rune (b* ((rule (car pred-rules))
                     (subclass (acl2::access acl2::rewrite-rule rule :subclass))
                     ((unless (eq subclass 'acl2::abbreviation)) nil)
                     (lhs (acl2::access acl2::rewrite-rule rule :lhs))
                     ((unless (and (consp (cadr lhs))
                                   (eq fix (car (cadr lhs)))
                                   (symbolp (cadr (cadr lhs)))))
                      nil)
                     (rhs (acl2::access acl2::rewrite-rule rule :rhs))
                     ((unless (equal rhs ''t)) nil)
                     (hyps (acl2::access acl2::rewrite-rule rule :hyps))
                     ((unless (atom hyps))
                      nil)
                     (equiv (acl2::access acl2::rewrite-rule rule :equiv))
                     ((unless (member equiv '(equal iff))) nil))
                  (acl2::access acl2::rewrite-rule rule :rune))))
      (if rune
          (mv t rune)
        (find-pred-of-fix-thm-aux fix pred (cdr pred-rules))))))

(defun find-unsigned-byte-p-pred-of-fix-thm-aux (fix pred size pred-rules)
  (if (atom pred-rules)
      (let ((body `(acl2::unsigned-byte-p (acl2::quote ,size) (,fix x))))
        (mv nil
            `(local (make-event
                     '(:or (defthm ,(intern-in-package-of-symbol
                                     (cat "TMP-DEFTYPES-" (symbol-name PRED) "-OF-" (symbol-name fix))
                                     'fty)
                             ,body)
                       (value-triple
                        (er hard? 'deftypes
                            "To use ~x0/~x1 as a fixing function/predicate, we must ~
                       be able to prove the following: ~x2.  But this proof ~
                       failed! Please try to prove this rule yourself."
                            ',fix ',pred ',body)))))))
    (let ((rune (b* ((rule (car pred-rules))
                     (subclass (acl2::access acl2::rewrite-rule rule :subclass))
                     ((unless (eq subclass 'acl2::abbreviation)) nil)
                     (lhs (acl2::access acl2::rewrite-rule rule :lhs))
                     ((unless (and (eq 'acl2::unsigned-byte-p (car lhs))
                                   (consp (cadr lhs))
                                   (eq (car (cadr lhs)) 'acl2::quote)
                                   (eq size (cadr (cadr lhs)))
                                   (consp (caddr lhs))
                                   (eq fix (car (caddr lhs)))
                                   (symbolp (cadr (caddr lhs)))))
                      nil)
                     (rhs (acl2::access acl2::rewrite-rule rule :rhs))
                     ((unless (equal rhs ''t)) nil)
                     (hyps (acl2::access acl2::rewrite-rule rule :hyps))
                     ((unless (atom hyps))
                      nil)
                     (equiv (acl2::access acl2::rewrite-rule rule :equiv))
                     ((unless (member equiv '(equal iff))) nil))
                  (acl2::access acl2::rewrite-rule rule :rune))))
      (if rune
          (mv t rune)
        (find-unsigned-byte-p-pred-of-fix-thm-aux fix pred size (cdr pred-rules))))))

(defun flextypes-collect-fix/pred-pairs-aux (types)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types))
              (flex*-collect-fix/pred-pairs x))
            (flextypes-collect-fix/pred-pairs-aux (cdr types)))))

(defun flextypes-collect-fix/pred-pairs (types)
  (remove-duplicates-equal (flextypes-collect-fix/pred-pairs-aux types)))


(defun collect-fix/pred-enable-rules (pairs world)
  ;; returns (mv runes-to-enable thms-to-admit)
  (if (atom pairs)
      (mv nil nil)
    (b* (((cons fix pred) (car pairs))
         (fix (acl2::deref-macro-name fix (acl2::macro-aliases world)))
         (pred (acl2::deref-macro-name pred (acl2::macro-aliases world)))
         (fix-exists (not (eq :none (getprop fix 'acl2::formals :none 'acl2::current-acl2-world world))))
         (pred-macro-args (getprop pred 'acl2::macro-args :none 'acl2::current-acl2-world world))
         (pred-macro-body (getprop pred 'acl2::macro-body nil 'acl2::current-acl2-world world))
         (unsigned-byte-p-pred-exists
          (and (not (eq :none pred-macro-args))
               (equal (car pred-macro-body) 'acl2::cons)
               (equal (cadr pred-macro-body) '(acl2::quote acl2::unsigned-byte-p))
               (consp (caddr pred-macro-body))
               (equal (car (caddr pred-macro-body)) 'acl2::cons)
               (consp (cadr (caddr pred-macro-body)))
               (equal (caadr (caddr pred-macro-body)) 'acl2::quote)
               (consp (cdadr (caddr pred-macro-body)))
               (natp (cadadr (caddr pred-macro-body)))
               (not (cddadr (caddr pred-macro-body)))
               (consp (caddr (caddr pred-macro-body)))
               (equal (car (caddr (caddr pred-macro-body))) 'acl2::cons)
               (consp (cdr (caddr (caddr pred-macro-body))))
               (equal (cadr (caddr (caddr pred-macro-body))) (car pred-macro-args))
               (consp (cddr (caddr (caddr pred-macro-body))))
               (equal (caddr (caddr (caddr pred-macro-body))) '(acl2::quote nil))
               (not (cdddr (caddr (caddr pred-macro-body))))
               (not (cdddr (caddr pred-macro-body)))
               (not (cdddr pred-macro-body))
          ))
         (pred-exists (or unsigned-byte-p-pred-exists
                          (not (eq :none (getprop pred 'acl2::formals :none 'acl2::current-acl2-world world)))))
         ((unless (and fix-exists pred-exists))
          ;; These pairs include types that we are about to define, so if the
          ;; function isn't yet defined, don't complain.  But if one is defined
          ;; but the other isn't, it's strange.
          (and (or fix-exists pred-exists)
               (cw "WARNING: ~x0 is defined but ~x1 is not"
                   (if fix-exists fix pred) (if fix-exists pred fix)))
          (collect-fix/pred-enable-rules (cdr pairs) world))
         (fix-rules (getprop fix 'acl2::lemmas nil 'acl2::current-acl2-world world))
         (pred-rules (getprop (if unsigned-byte-p-pred-exists
                                  'acl2::unsigned-byte-p
                                pred)
                              'acl2::lemmas nil 'acl2::current-acl2-world world))
         ((mv fix-rule-exists fix-rule)
          (if unsigned-byte-p-pred-exists
              (find-fix-when-unsigned-byte-p-pred-thm-aux fix pred (cadadr (caddr pred-macro-body)) fix-rules)
              (find-fix-when-pred-thm-aux fix pred fix-rules)))
         ((mv pred-rule-exists pred-rule)
          (if unsigned-byte-p-pred-exists
              (find-unsigned-byte-p-pred-of-fix-thm-aux fix pred (cadadr (caddr pred-macro-body)) pred-rules)
            (find-pred-of-fix-thm-aux fix pred pred-rules)))
         ((mv enables thms)
          (collect-fix/pred-enable-rules (cdr pairs) world))
         ((mv enables thms)
          (if fix-rule-exists
              (mv (cons fix-rule enables) thms)
            (mv enables (cons fix-rule thms))))
         ((mv enables thms)
          (if pred-rule-exists
              (mv (cons pred-rule enables) thms)
            (mv enables (cons pred-rule thms)))))
      (mv enables thms))))

;; ------------------ Deftypes-events -----------------------
;; --- Flextype-collect-events ---
(defun flextypelist-append-events (kwd types)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types))
              (cdr (assoc kwd x.kwd-alist)))
            (flextypelist-append-events kwd (cdr types)))))

(defun flextype-collect-events (kwd kwd-alist types)
  (append (getarg kwd nil kwd-alist)
          (flextypelist-append-events kwd types)))

(defun flextypelist-collect-enable-rules (types)
  (if (atom types)
      nil
    (append (with-flextype-bindings (x (car types))
              (cdr (assoc :enable-rules x.kwd-alist)))
            (flextypelist-collect-enable-rules (cdr types)))))

(defun flextypes-collect-enable-rules (x)
  (append (cdr (assoc :enable-rules (flextypes->kwd-alist x)))
          (flextypelist-collect-enable-rules (flextypes->types x))))

(defun collect-uncond-type-prescriptions-from-list (x ens)
  (if (atom x)
      nil
    (if (and (acl2::enabled-numep
              (acl2::access acl2::type-prescription (car x) :nume) ens)
             (not (acl2::access acl2::type-prescription (car x) :hyps)))
        (let ((rune (acl2::access acl2::type-prescription (car x) :rune)))
          (if (eq (car rune) :type-prescription)
              (cons rune
                    (collect-uncond-type-prescriptions-from-list (cdr x) ens))
            (collect-uncond-type-prescriptions-from-list (cdr x) ens)))
      (collect-uncond-type-prescriptions-from-list (cdr x) ens))))


(defun collect-uncond-type-prescriptions (wrld ens fns-seen)
  (declare (xargs :guard (plist-worldp wrld)))
  (if (atom wrld)
      nil
    (b* (((list* sym key val) (car wrld))
         ((unless (eq key 'acl2::type-prescriptions))
          (collect-uncond-type-prescriptions (cdr wrld) ens fns-seen))
         ((when (hons-get sym fns-seen))
          (collect-uncond-type-prescriptions (cdr wrld) ens fns-seen)))
      (append (collect-uncond-type-prescriptions-from-list val ens)
              (collect-uncond-type-prescriptions
               (cdr wrld) ens (hons-acons sym t fns-seen))))))





(defun deftypes-events (x state)
  (b* (((flextypes x) x)
       (fix/pred-pairs (flextypes-collect-fix/pred-pairs x.types))
       ((mv enable-rules temp-thms) (collect-fix/pred-enable-rules fix/pred-pairs (w state)))
       (verbosep (getarg :verbosep nil x.kwd-alist)))
    `(with-output
       ,@(and (not verbosep)
              `(:off (prove event observation)
                :summary (acl2::form acl2::time)))
       (encapsulate nil       ;; was: defsection ,x.name
         (with-output
           ,@(and (not verbosep)
                  `(:summary (acl2::form acl2::time)))
           (progn
             (local (table xdoc::xdoc 'xdoc::post-defxdoc-event nil))
             (local (std::set-returnspec-mrec-default-hints nil))
             (local (std::set-returnspec-default-hints nil))
             (local (fty::set-deffixequiv-default-hints nil))
             (local (fty::set-deffixequiv-mutual-default-hints nil))
             (local (deftheory deftypes-orig-theory (current-theory :here)))
             ,@(flextype-collect-events :prepwork x.kwd-alist x.types)
             (local (set-inhibit-warnings "disable" "subsume" "non-rec" "double-rewrite"))
             (set-bogus-defun-hints-ok t)
             (set-ignore-ok t)
             (set-irrelevant-formals-ok t)
             (local (make-event
                     `(deftheory deftypes-type-theory
                        ',(collect-uncond-type-prescriptions
                           (w state) (acl2::ens state) nil))))
             (local (deflabel deftypes-before-temp-thms))
             (progn . ,temp-thms)
             (local (deftheory deftypes-temp-thms
                      (set-difference-theories
                       (current-theory :here)
                       (current-theory 'deftypes-before-temp-thms))))
             (local (in-theory (disable deftypes-orig-theory)))
             (local (in-theory (enable deftypes-type-theory)))
             (local (in-theory (acl2::enable* deftypes-theory
                                              ,@(flextypes-collect-enable-rules x)
                                              . ,enable-rules)))
             (local (set-default-hints
                     '((and stable-under-simplificationp
                            '(:in-theory (enable deftypes-orig-theory))))))
             ;; Don't try to automatically define equivalences while we're setting up types
             (local (std::remove-default-post-define-hook :fix))

             ,@(flextypes-predicate-def x)

             ,@(flextype-collect-events :post-pred-events x.kwd-alist x.types)

             ,@(flextype-def-sum-kinds x.types)

             ,@(flextypes-fix-def x)

             ,@(flextype-collect-events :post-fix-events x.kwd-alist x.types)

             ,@(flextypes-sum-accessor/constructors x.types x.types)

             (local (in-theory (disable . ,(flextypes-fns x.types))))

             ,@(flextypes-count x)

             (local (in-theory (enable deftypes-orig-theory)))
             (local (set-default-hints nil))

             ,@(flextype-collect-events :post-events x.kwd-alist x.types)

             ,@(flextype-collect-events :///-events x.kwd-alist x.types)

             (add-flextype ,x)

             . ,(flextypes-defxdoc x (w state))))))))

;; ------------------ Interface Macros -----------------------
(defun deftypes-fn (args state)
  (b* ((x (parse-flextypes args state)))
    (deftypes-events x state)))

(defmacro deftypes (&rest args)
  `(make-event (deftypes-fn ',args state)))

(defun flextypes-kwd-alist-from-specialized-kwd-alist (kwd-alist)
  (if (getarg :verbosep nil kwd-alist)
      '((:verbosep . t))
    nil))

(defun defflexsum-fn (whole state)
  (b* ((our-fixtypes (list (flextype-form->fixtype whole)))
       (fixtype-al (append our-fixtypes
                           (get-fixtypes-alist (w state))))
       (x (parse-flexsum (cdr whole) nil our-fixtypes fixtype-al))
       (x (if (or (flexsum->recp x)
                  (member :count (cdr whole)))
              x
            ;; don't make a count if it's not recursive
            (change-flexsum x :count nil)))
       ((flexsum x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)
                                  :no-count (not x.count)
                                  :kwd-alist (flextypes-kwd-alist-from-specialized-kwd-alist x.kwd-alist)
                                  :recp x.recp)))
    (deftypes-events flextypes state)))

(defmacro defflexsum (&whole form &rest args)
  (declare (ignore args))
  `(make-event (defflexsum-fn ',form state)))

(defun deflist-fn (whole state)
  (b* ((our-fixtypes (list (flextype-form->fixtype whole)))
       (fixtype-al (append our-fixtypes
                           (get-fixtypes-alist (w state))))
       (x (parse-flexlist (cdr whole) nil our-fixtypes fixtype-al state))
       (x (if (or (flexlist->recp x)
                  (member :count (cdr whole)))
              x
            (change-flexlist x :count nil)))
       ((flexlist x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)
                                  :no-count (not x.count)
                                  :kwd-alist (flextypes-kwd-alist-from-specialized-kwd-alist x.kwd-alist)
                                  :recp x.recp)))
    (deftypes-events flextypes state)))

(defmacro deflist (&whole form &rest args)
  (declare (ignore args))
  `(make-event (deflist-fn ',form state)))

(defun defalist-fn (whole state)
  (b* ((our-fixtypes (list (flextype-form->fixtype whole)))
       (fixtype-al (append our-fixtypes
                           (get-fixtypes-alist (w state))))
       (x (parse-flexalist (cdr whole) nil our-fixtypes fixtype-al state))
       (x (if (or (flexalist->recp x)
                  (member :count (cdr whole)))
              x
            (change-flexalist x :count nil)))
       ((flexalist x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)
                                  :no-count (not x.count)
                                  :kwd-alist (flextypes-kwd-alist-from-specialized-kwd-alist x.kwd-alist)
                                  :recp x.recp)))
    (deftypes-events flextypes state)))

(defmacro defalist (&whole form &rest args)
  (declare (ignore args))
  `(make-event (defalist-fn ',form state)))

(defun defmap-fn (whole state)
  (b* ((our-fixtypes (list (flextype-form->fixtype whole)))
       (fixtype-al (append our-fixtypes
                           (get-fixtypes-alist (w state))))
       (x (parse-flexalist (cdr whole) nil our-fixtypes fixtype-al state))
       (x (change-flexalist x :strategy :drop-keys))
       (x (if (or (flexalist->recp x)
                  (member :count (cdr whole)))
              x
            (change-flexalist x :count nil)))
       ((flexalist x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)
                                  :no-count (not x.count)
                                  :kwd-alist (flextypes-kwd-alist-from-specialized-kwd-alist x.kwd-alist)
                                  :recp x.recp)))
    (deftypes-events flextypes state)))

(defmacro defmap (&whole form &rest args)
  (declare (ignore args))
  `(make-event (defmap-fn ',form state)))

(defun deftagsum-fn (whole state)
  (b* ((fixtype (flextype-form->fixtype whole))
       (fixtype-al (cons fixtype
                         (get-fixtypes-alist (w state))))
       (x (parse-tagsum (cdr whole) nil (list fixtype) fixtype-al))
       (x (if (or (flexsum->recp x)
                  (member :count (cdr whole)))
              x
            ;; don't make a count if it's not recursive
            (change-flexsum x :count nil)))
       ((flexsum x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)
                                  :no-count (not x.count)
                                  :kwd-alist (flextypes-kwd-alist-from-specialized-kwd-alist x.kwd-alist)
                                  :recp x.recp)))
    (deftypes-events flextypes state)))

(defmacro deftagsum (&whole form &rest args)
  (declare (ignore args))
  `(make-event (deftagsum-fn ',form state)))

(defun defoption-fn (whole state)
  (b* ((fixtype (flextype-form->fixtype whole))
       (fixtype-al (cons fixtype
                         (get-fixtypes-alist (w state))))
       (x (parse-option (cdr whole) nil (list fixtype) fixtype-al))
       (x (if (or (flexsum->recp x)
                  (member :count (cdr whole)))
              x
            ;; don't make a count if it's not recursive
            (change-flexsum x :count nil)))
       ((flexsum x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)
                                  :no-count (not x.count)
                                  :kwd-alist (flextypes-kwd-alist-from-specialized-kwd-alist x.kwd-alist)
                                  :recp x.recp)))
    (deftypes-events flextypes state)))


(defmacro defoption (&whole form &rest args)
  (declare (ignore args))
  `(make-event (defoption-fn ',form state)))


(defun deftranssum-fn (whole state)
  (b* ((fixtype (flextype-form->fixtype whole))
       (fixtype-al (cons fixtype
                         (get-fixtypes-alist (w state))))
       (x (parse-transsum (cdr whole) nil (list fixtype) fixtype-al state))
       ;; bozo this is really gross.  what are we doing?
       (x (if (or (flextranssum->recp x)
                  (member :count (cdr whole)))
              x
            ;; don't make a count if it's not recursive
            (change-flextranssum x :count nil)))
       ((flextranssum x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)
                                  :no-count (not x.count)
                                  :kwd-alist (flextypes-kwd-alist-from-specialized-kwd-alist x.kwd-alist)
                                  :recp x.recp)))
    (deftypes-events flextypes state)))

(defmacro deftranssum (&whole form &rest args)
  (declare (ignore args))
  `(make-event (deftranssum-fn ',form state)))




(defun defprod-fn (whole state)
  (b* ((fixtype (flextype-form->fixtype whole))
       (fixtype-al (cons fixtype
                         (get-fixtypes-alist (w state))))
       (x (parse-defprod (cdr whole) nil (list fixtype) fixtype-al))
       (x (if (member :count (cdr whole))
              x
            (change-flexsum x :count nil))) ;; no count for a single product
       ((flexsum x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)
                                  :kwd-alist (flextypes-kwd-alist-from-specialized-kwd-alist x.kwd-alist)
                                  :no-count (not x.count)
                                  :recp x.recp)))
    (deftypes-events flextypes state)))

(defmacro defprod (&whole form &rest args)
  (declare (ignore args))
  `(make-event (defprod-fn ',form state)))


(defun defset-fn (whole state)
  (b* ((our-fixtypes (list (flextype-form->fixtype whole)))
       (fixtype-al (append our-fixtypes
                           (get-fixtypes-alist (w state))))
       (x (parse-flexset (cdr whole) nil our-fixtypes fixtype-al state))
       (x (if (member :count (cdr whole))
              x
            (change-flexset x :count nil)))
       ((flexset x) x)
       (flextypes (make-flextypes :name x.name
                                  :types (list x)
                                  :no-count (not x.count)
                                  :kwd-alist (flextypes-kwd-alist-from-specialized-kwd-alist x.kwd-alist)
                                  :recp x.recp)))
    (deftypes-events flextypes state)))

(defmacro defset (&whole form &rest args)
  (declare (ignore args))
  `(make-event (defset-fn ',form state)))
