; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../expr")
(include-book "../util/defs")
(local (include-book "../util/arithmetic"))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (non-parallel-book))

(defxdoc expr-tools
  :parents (mlib)
  :short "Basic functions for working with expressions.")

(local (xdoc::set-default-parents expr-tools))

(defthm vl-maybe-expr-fix-when-exists
  (implies x
           (equal (vl-maybe-expr-fix x)
                  (vl-expr-fix x)))
  :hints(("Goal" :in-theory (enable vl-maybe-expr-fix))))

(defthm vl-expr-fix-under-vl-maybe-expr-equiv-when-exists
  (implies x
           (vl-maybe-expr-equiv (vl-expr-fix x)
                                x))
  :hints(("Goal" :in-theory (enable vl-maybe-expr-fix))))

;; (defthm vl-atts-fix-when-atom
;;   (implies (atom x)
;;            (equal (vl-atts-fix x)
;;                   nil))
;;   :hints(("Goal" :in-theory (enable vl-atts-fix))))

(defthm vl-atts-fix-of-cons
  (equal (vl-atts-fix (cons a x))
         (if (atom a)
             (vl-atts-fix x)
           (cons (cons (str-fix (car a))
                       (vl-maybe-expr-fix (cdr a)))
                 (vl-atts-fix x))))
  :hints(("Goal" :in-theory (enable vl-atts-fix))))

;; (defines vl-expr-count
;;   :short "A measure for recurring over expressions."
;;   :long "<p>This measure has a few nice properties.  It respects all of the
;; equivalences for expressions and avoids having a function for @(see
;; vl-maybe-expr-p).</p>

;; <p>Note that we don't count the attributes of an atom.  Normally there's not
;; any reason to descend into their attributes, so this doesn't really matter.  We
;; might some day extend this function to also count atom attributes.</p>"

;;   :verify-guards nil
;;   :flag vl-expr-flag ;; BOZO no way to override this on deftypes
;;   :flag-local nil
;;   :prepwork
;;   ((local (defrule vl-exprlist-count-raw-of-vl-nonatom->args-rw
;;             (implies (eq (vl-expr-kind x) :nonatom)
;;                      (< (vl-exprlist-count-raw (vl-nonatom->args x))
;;                         (vl-expr-count-raw x)))
;;             :rule-classes :rewrite))

;;    (local (defrule vl-exprlist-count-raw-of-cdr-weak
;;             (<= (vl-exprlist-count-raw (cdr x))
;;                 (vl-exprlist-count-raw x))
;;             :rule-classes ((:rewrite) (:linear))))

;;    (local (defrule vl-exprlist-count-raw-of-cdr-rw
;;             (implies (consp x)
;;                      (< (vl-exprlist-count-raw (cdr x))
;;                         (vl-exprlist-count-raw x)))
;;             :rule-classes :rewrite))

;;    (local (defrule vl-expr-count-raw-less-than-atts
;;             ;; BOZO really gross
;;             (implies x
;;                      (< (vl-expr-count-raw x)
;;                         (vl-atts-count-raw (cons (cons name x) alist))))
;;             :in-theory (enable vl-atts-count-raw vl-maybe-expr-expr->expr)
;;             :expand ((vl-maybe-expr-count-raw x))))

;;    (local (defthm vl-maybe-expr-count-raw-of-vl-expr-fix
;;             (implies x
;;                      (equal (vl-maybe-expr-count-raw (vl-expr-fix x))
;;                             (vl-maybe-expr-count-raw x)))
;;             :hints(("Goal" :in-theory (enable vl-maybe-expr-count-raw))))))

;;   (define vl-expr-count ((x vl-expr-p))
;;     :measure (two-nats-measure (vl-expr-count-raw x) 0)
;;     :flag :expr
;;     (vl-expr-case x
;;       :atom
;;       1
;;       :nonatom
;;       (+ 1
;;          (vl-atts-count x.atts)
;;          (vl-exprlist-count x.args))))

;;   (define vl-atts-count ((x vl-atts-p))
;;     :measure (two-nats-measure (vl-atts-count-raw x) (len x))
;;     :flag :atts
;;     (cond ((atom x)
;;            1)
;;           ((atom (car x))
;;            (vl-atts-count (cdr x)))
;;           ((cdar x)
;;            (+ 1
;;               (vl-expr-count (cdar x))
;;               (vl-atts-count (cdr x))))
;;           (t
;;            (+ 1
;;               (vl-atts-count (cdr x))))))

;;   (define vl-exprlist-count ((x vl-exprlist-p))
;;     :measure (two-nats-measure (vl-exprlist-count-raw x) 0)
;;     :flag :list
;;     (if (atom x)
;;         1
;;       (+ 1
;;          (vl-expr-count (car x))
;;          (vl-exprlist-count (cdr x)))))

;;   ///

;;   (local (in-theory (enable vl-expr-count
;;                             vl-atts-count
;;                             vl-exprlist-count)))

;;   (defrule vl-exprlist-count-of-cons
;;     (equal (vl-exprlist-count (cons a x))
;;            (+ 1
;;               (vl-expr-count a)
;;               (vl-exprlist-count x))))

;;   (defrule vl-expr-count-of-car-weak
;;     (<= (vl-expr-count (car x))
;;         (vl-exprlist-count x))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defrule vl-expr-count-of-car-strong
;;     (implies (consp x)
;;              (< (vl-expr-count (car x))
;;                 (vl-exprlist-count x)))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defthm vl-expr-kind-when-vl-expr-count-is-1-fwd
;;     ;; Goofy rule that helps with, e.g., vl-pp-expr
;;     (implies (equal (vl-expr-count x) 1)
;;              (equal (vl-expr-kind x) :atom))
;;     :rule-classes ((:forward-chaining))
;;     :hints(("Goal"
;;             :expand (vl-expr-count x)
;;             :in-theory (enable vl-expr-count))))

;;   (defrule vl-exprlist-count-of-cdr-weak
;;     (<= (vl-exprlist-count (cdr x))
;;         (vl-exprlist-count x))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defrule vl-exprlist-count-of-cdr-strong
;;     (implies (consp x)
;;              (< (vl-exprlist-count (cdr x))
;;                 (vl-exprlist-count x)))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defrule vl-atts-count-when-atom
;;     (implies (atom x)
;;              (equal (vl-atts-count x)
;;                     1)))

;;   (defrule vl-atts-count-of-cons
;;     (equal (vl-atts-count (cons a x))
;;            (if (atom a)
;;                (vl-atts-count x)
;;              (+ 1
;;                 (if (cdr a) (vl-expr-count (cdr a)) 0)
;;                 (vl-atts-count x)))))

;;   (defrule vl-atts-count-of-cdr-weak
;;     (<= (vl-atts-count (cdr x))
;;         (vl-atts-count x))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defrule vl-atts-count-of-cdr-strong
;;     (implies (and (consp x)
;;                   (consp (car x)))
;;              (< (vl-atts-count (cdr x))
;;                 (vl-atts-count x)))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defthm vl-expr-count-of-cdar-when-vl-atts-p
;;     (implies (and (vl-atts-p x) x)
;;              (< (vl-expr-count (cdar x))
;;                 (vl-atts-count x)))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defrule vl-exprlist-count-of-vl-nonatom->args-strong
;;     (implies (equal (vl-expr-kind x) :nonatom)
;;              (< (vl-exprlist-count (vl-nonatom->args x))
;;                 (vl-expr-count x)))
;;     :rule-classes ((:rewrite) (:linear))
;;     :expand (vl-expr-count x))

;;   (defrule vl-exprlist-count-of-vl-nonatom->atts-strong
;;     (implies (equal (vl-expr-kind x) :nonatom)
;;              (< (vl-atts-count (vl-nonatom->atts x))
;;                 (vl-expr-count x)))
;;     :rule-classes ((:rewrite) (:linear))
;;     :expand (vl-expr-count x))

;;   (deffixequiv-mutual vl-expr-count
;;     :hints(("Goal"
;;             :expand (vl-atts-count x)
;;             :in-theory (enable vl-expr-count
;;                                vl-atts-count
;;                                vl-exprlist-count
;;                                vl-atts-fix
;;                                vl-exprlist-fix)))))


;; (encapsulate
;;   ()

;;   ;; A tricky recursion over expressions, to make sure our measure is good
;;   ;; enough to handle lots of cases.  Doesn't compute anything useful.

;;   (local (defines vl-expr-recursion-test
;;            (define f-expr ((x vl-expr-p))
;;              :measure (two-nats-measure (vl-expr-count x) 2)
;;              (vl-expr-case x
;;                :atom 1
;;                :nonatom
;;                (+ (case x.op
;;                     ;; Explicit arg recursions for known arity operators
;;                     (:vl-unary-plus   (+ 1 (f-expr (first x.args))))
;;                     (:vl-binary-plus  (+ (f-expr (first x.args))
;;                                          (f-expr (second x.args))))
;;                     (:vl-qmark        (+ (f-expr (first x.args))
;;                                          (f-expr (second x.args))
;;                                          (f-expr (third x.args))))
;;                     (otherwise 0))
;;                   ;; Recursion on all args
;;                   (f-exprlist x.args)
;;                   ;; Recursion on all atts
;;                   (f-atts x.atts))))

;;            (define f-atts-aux ((x vl-atts-p))
;;              :measure (two-nats-measure (vl-atts-count x) (len x))
;;              (b* (((when (atom x))
;;                    0)
;;                   ;; NOTE: when recurring through attributes you always obey the non-alist
;;                   ;; convention to match the equivalence relation.  See :doc std/alists if
;;                   ;; you don't understand this convention.
;;                   ((when (atom (car x)))
;;                    (f-atts-aux (cdr x)))
;;                   ((cons ?name expr) (car x)))
;;                (+ 1
;;                   (if expr (f-expr expr) 1)
;;                   (f-atts-aux (cdr x)))))

;;            (define f-atts ((x vl-atts-p))
;;              :measure (two-nats-measure (vl-atts-count x) (+ 1 (len x)))
;;              (f-atts-aux x))

;;            (define f-exprlist-aux ((x vl-exprlist-p))
;;              :measure (two-nats-measure (vl-exprlist-count x) 0)
;;              (if (atom x)
;;                  1
;;                (+ (f-expr (car x))
;;                   (f-exprlist-aux (cdr x)))))

;;            (define f-exprlist ((x vl-exprlist-p))
;;              :measure (two-nats-measure (vl-exprlist-count x) 1)
;;              (f-exprlist-aux x))
;;            ///
;;            (local (in-theory (enable vl-atts-fix)))
;;            (local (fty::set-deffixequiv-mutual-default-hints nil))
;;            (deffixequiv-mutual vl-expr-recursion-test))))


;; (defines vl-expr-count-noatts
;;   :short "A measure for recurring over expressions but ignoring attributes."

;;   (define vl-expr-count-noatts ((x vl-expr-p))
;;     :measure (vl-expr-count x)
;;     :flag :expr
;;     (vl-expr-case x
;;       :atom 1
;;       :nonatom
;;       (+ 1 (vl-exprlist-count-noatts x.args))))

;;   (define vl-exprlist-count-noatts ((x vl-exprlist-p))
;;     :measure (vl-exprlist-count x)
;;     :flag :list
;;     (if (atom x)
;;         1
;;       (+ 1
;;          (vl-expr-count-noatts (car x))
;;          (vl-exprlist-count-noatts (cdr x)))))
;;   ///
;;   (defrule vl-exprlist-count-noatts-of-cons
;;     (equal (vl-exprlist-count-noatts (cons a x))
;;            (+ 1
;;               (vl-expr-count-noatts a)
;;               (vl-exprlist-count-noatts x))))

;;   (defrule vl-expr-count-noatts-of-car-weak
;;     (<= (vl-expr-count-noatts (car x))
;;         (vl-exprlist-count-noatts x))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defrule vl-expr-count-noatts-of-car-strong
;;     (implies (consp x)
;;              (< (vl-expr-count-noatts (car x))
;;                 (vl-exprlist-count-noatts x)))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defthm vl-expr-kind-when-vl-expr-count-noatts-is-1-fwd
;;     ;; Goofy rule that helps with, e.g., vl-pp-expr
;;     (implies (equal (vl-expr-count-noatts x) 1)
;;              (equal (vl-expr-kind x) :atom))
;;     :rule-classes ((:forward-chaining))
;;     :hints(("Goal"
;;             :expand (vl-expr-count-noatts x)
;;             :in-theory (enable vl-expr-count-noatts))))

;;   (defrule vl-exprlist-count-noatts-of-cdr-weak
;;     (<= (vl-exprlist-count-noatts (cdr x))
;;         (vl-exprlist-count-noatts x))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defrule vl-exprlist-count-noatts-of-cdr-strong
;;     (implies (consp x)
;;              (< (vl-exprlist-count-noatts (cdr x))
;;                 (vl-exprlist-count-noatts x)))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defrule vl-exprlist-count-noatts-of-vl-nonatom->args-strong
;;     (implies (equal (vl-expr-kind x) :nonatom)
;;              (< (vl-exprlist-count-noatts (vl-nonatom->args x))
;;                 (vl-expr-count-noatts x)))
;;     :rule-classes ((:rewrite) (:linear))
;;     :expand (vl-expr-count-noatts x))

;;   (deffixequiv-mutual vl-expr-count-noatts))





;; (local
;;  (encapsulate nil
;;    (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
;;    (local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
;;    (local (in-theory (disable ACL2::|(integer-length (floor n 2))|)))
;;    ;; (local (defthm integer-length-when-floor-<=-2
;;    ;;          (implies (and (natp n)
;;    ;;                        (<= (floor n 2) 2))
;;    ;;                   (<= (integer-length n) 3))
;;    ;;          :hints (("goal" :expand ((integer-length n)
;;    ;;                                   (integer-length (floor n 2)))
;;    ;;                   :in-theory (enable acl2::logcdr)))))
;;    (defthm integer-length-less-than-number
;;      (implies (natp n)
;;               (and (<= (integer-length n) n)
;;                    (implies (< 2 n)
;;                             (< (integer-length n) n))))
;;      :hints(("Goal" :in-theory (e/d (acl2::ihsext-inductions
;;                                        acl2::logcdr)
;;                                     (ifix))
;;              :induct (integer-length n))
;;             (and stable-under-simplificationp
;;                  '(:expand ((integer-length n))))))))


(defsection vl-one-bit-constants
  :short "Already-sized, one-bit constants."
  :long "<p>The names of these constants are historic relics from a time when
VL's expressions had size annotations.  We should probably get rid of these, it
looks like they are now mainly used in @(see udp-elim).</p>"

  (defconst |*sized-1'b0*|
    (hons-copy (make-vl-literal
                :val
                (make-vl-constint :value 0
                                  :origwidth 1
                                  :origsign :vl-unsigned))))

  (defconst |*sized-1'b1*|
    (hons-copy (make-vl-literal
                :val
                (make-vl-constint :value 1
                                  :origwidth 1
                                  :origsign :vl-unsigned))))

  (defconst |*sized-1'bx*|
    (hons-copy (make-vl-literal :val (make-vl-weirdint :bits (list :vl-xval)
                                                       :origsign :vl-unsigned))))

  (defconst |*sized-1'bz*|
    (hons-copy (make-vl-literal :val (make-vl-weirdint :bits (list :vl-zval)
                                                       :origsign :vl-unsigned)))))



(define vl-expr-resolved-p ((x vl-expr-p))
  :short "Recognizes plain constant integer expressions."

  :long "<p>We say an expression is <b>resolved</b> when it is just an atomic,
integer value that is free of X/Z bits.  We often expect to be able to resolve
the expressions that occur in ranges like @('wire [3:0] foo;') and in
selects.</p>"
  :inline t
  (vl-expr-case x
    :vl-literal (vl-value-case x.val :vl-constint)
    :otherwise nil))

(define vl-resolved->val ((x vl-expr-p))
  :guard (vl-expr-resolved-p x)
  :returns (val integerp :rule-classes :type-prescription)
  :short "Get the value from a resolved expression."
  (b* (((vl-constint x) (vl-literal->val x)))
    (if (eq x.origsign :vl-signed)
        (acl2::logext x.origwidth x.value)
      x.value))
  :guard-hints (("Goal" :in-theory (enable vl-expr-resolved-p))))

(deflist vl-exprlist-resolved-p (x)
  (vl-expr-resolved-p x)
  :guard (vl-exprlist-p x))

(defprojection vl-exprlist-resolved->vals ((x vl-exprlist-p))
  :guard (vl-exprlist-resolved-p x)
  :returns (vals integer-listp)
  (vl-resolved->val x))


(define vl-idscope-p ((x vl-scopeexpr-p))
  :short "Recognize a scopeexpr that is just a plain identifier."
  (vl-scopeexpr-case x
    :end (vl-hidexpr-case x.hid :end)
    :otherwise nil))

(define vl-idexpr-p ((x vl-expr-p))
  :short "Recognize plain identifier expressions."
  :long "<p>This recognizes simple non-hierarchical identifier expressions
like @('foo').</p>"
  :inline t
  (vl-expr-case x
    :vl-index (and (atom x.indices)
                   (vl-partselect-case x.part :none)
                   (vl-idscope-p x.scope))
    :otherwise nil))

(deflist vl-idexprlist-p (x)
  (vl-idexpr-p x)
  :guard (vl-exprlist-p x))


(define vl-idscope->name ((x vl-scopeexpr-p))
  :guard (vl-idscope-p x)
  :prepwork ((local (in-theory (enable vl-idscope-p))))
  :returns (name stringp :rule-classes :type-prescription)
  (vl-hidexpr-end->name (vl-scopeexpr-end->hid x)))

(define vl-idexpr->name ((x vl-expr-p))
  :returns (name stringp :rule-classes :type-prescription)
  :guard (vl-idexpr-p x)
  :short "Get the name from a @(see vl-idexpr-p)."
  :long "<p>Guaranteed to return a string.</p>"
  :inline t
  (vl-idscope->name (vl-index->scope x))
  :guard-hints(("Goal" :in-theory (enable vl-idexpr-p))))

(defprojection vl-idexprlist->names ((x vl-exprlist-p))
  :returns (names string-listp)
  :guard (vl-idexprlist-p x)
  (vl-idexpr->name x))


(define vl-idscope ((name stringp))
  :returns (scopeexpr vl-scopeexpr-p)
  (make-vl-scopeexpr-end :hid (make-vl-hidexpr-end :name name))
  ///
  (defret vl-idscope-p-of-vl-idscope
    (vl-idscope-p scopeexpr)
    :hints(("Goal" :in-theory (enable vl-idscope-p))))

  (defret vl-idscope->name-of-vl-idscope
    (equal (vl-idscope->name scopeexpr) (string-fix name))
    :hints(("Goal" :in-theory (enable vl-idscope->name)))))

(define vl-idexpr ((name stringp))
  :returns (expr vl-expr-p)
  :short "Construct an @(see vl-idexpr-p)."
  :long "<p>@(call vl-idexpr) constructs a simple identifier expression with
the given name, width, and type.</p>

<p>I didn't always hons these, but now it seems like a good idea since the same
identifier may be needed in several contexts, and since we often want to
construct fast alists binding identifiers to things, etc.</p>"
  :inline t
  (hons-copy
   (make-vl-index :scope (vl-idscope name)
                  :indices nil
                  :part (make-vl-partselect-none)))
  ///
  (local (in-theory (enable vl-idexpr-p vl-idexpr->name)))

  (defthm vl-idexpr-p-of-vl-idexpr
    (vl-idexpr-p (vl-idexpr name)))

  (defthm vl-idexpr->name-of-vl-idexpr
    (equal (vl-idexpr->name (vl-idexpr name))
           (str-fix name)))

  ;; (defthm vl-expr->type-of-vl-idexpr
  ;;   (equal (vl-expr->type (vl-idexpr name type))
  ;;          (vl-maybe-datatype-fix type)))

  (defthm vl-expr-kind-of-vl-idexpr
    (equal (vl-expr-kind (vl-idexpr name))
           :vl-index)))


(defprojection vl-make-idexpr-list ((x          string-listp))
  :returns (exprs (and (vl-exprlist-p exprs)
                       (vl-idexprlist-p exprs)))
  (vl-idexpr x)
  :long "<p>Each expression is given the specified @('finalwidth') and
@('finaltype').</p>"
  ///
  (defthm vl-idexprlist->names-of-vl-make-idexpr-list
    (implies (force (string-listp x))
             (equal (vl-idexprlist->names (vl-make-idexpr-list x))
                    x))))

;; (define replace-list-entries (x y)
;;   :guard (<= (len x) (len y))
;;   (if (atom x)
;;       x
;;     (cons (car y)
;;           (replace-list-entries (cdr x) (cdr y))))
;;   ///
;;   (defthm vl-exprlist-p-of-replace-list-entries
;;     (implies (and (vl-exprlist-p y)
;;                   (<= (len x) (len y)))
;;              (vl-exprlist-p (replace-list-entries x y))))

;;   (defthm replace-list-entries-of-append
;;     (equal (replace-list-entries a (append a b))
;;            a))

;;   (defthm replace-list-entries-of-self
;;     (equal (replace-list-entries a a)
;;            a)))

(local (defthm vl-exprlist-count-of-append
         (equal (vl-exprlist-count (append a b))
                (+ -1 (vl-exprlist-count a) (vl-exprlist-count b)))
         :hints(("Goal" :in-theory (enable vl-exprlist-count append)))))

(local (defthm vl-exprlist-count-of-cons-rw
         (equal (vl-exprlist-count (cons a b))
                (+ 1 (vl-expr-count a) (vl-exprlist-count b)))
         :hints(("Goal" :in-theory (enable vl-exprlist-count)))))

(define vl-hidexpr->subexprs ((x vl-hidexpr-p))
  :returns (subexprs vl-exprlist-p)
  :measure (vl-hidexpr-count x)
  (vl-hidexpr-case x
    :end nil
    :dot (append-without-guard (vl-hidindex->indices x.first)
                               (vl-hidexpr->subexprs x.rest)))
  ///
  (defret vl-hidexpr->subexprs-true-listp
    (true-listp (vl-hidexpr->subexprs x))
    :rule-classes :type-prescription)
  (defret vl-exprlist-count-of-vl-hidexpr->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-hidexpr-count x))
    :hints (("goal" :induct t
             :in-theory (enable vl-hidexpr-count)))
    :rule-classes :linear))

(local (defthm exprlist-fix-of-take
         (implies (<= (nfix n) (len x))
                  (equal (vl-exprlist-fix (take n x))
                         (take n (vl-exprlist-fix x))))))
(local (in-theory (disable vl-exprlist-fix-of-take)))

(define vl-hidexpr-update-subexprs ((x vl-hidexpr-p)
                                    (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-hidexpr->subexprs x)))
  :verify-guards nil
  :measure (vl-hidexpr-count x)
  :returns (new-x vl-hidexpr-p)
  (vl-hidexpr-case x
    :end (vl-hidexpr-fix x)
    :dot (b* (((vl-hidindex x.first))
              (nsubexprs (len x.first.indices))
              (subexprs (vl-exprlist-fix subexprs)))
           (change-vl-hidexpr-dot
            x :first (change-vl-hidindex
                      x.first
                      :indices (take nsubexprs subexprs))
            :rest (vl-hidexpr-update-subexprs x.rest (nthcdr nsubexprs subexprs)))))
  ///
  (verify-guards vl-hidexpr-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-hidexpr->subexprs x))))))

  (defthm vl-hidexpr-update-subexprs-identity
    (equal (vl-hidexpr-update-subexprs x (vl-hidexpr->subexprs x))
           (vl-hidexpr-fix x))
    :hints(("Goal" :in-theory (enable vl-hidexpr->subexprs)
            :induct t)))

  (defthm vl-hidexpr-update-subexprs-identity2
    (implies (equal (len y) (len (vl-hidexpr->subexprs x)))
             (equal (vl-hidexpr->subexprs (vl-hidexpr-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-hidexpr->subexprs)
            :induct t))))

(define vl-scopeexpr->subexprs ((x vl-scopeexpr-p))
  :returns (subexprs vl-exprlist-p)
  :measure (vl-scopeexpr-count x)
  (vl-scopeexpr-case x
    :end (vl-hidexpr->subexprs x.hid)
    :colon (vl-scopeexpr->subexprs x.rest))
  ///
  (defret vl-exprlist-count-of-vl-scopeexpr->subexprs
    (< (vl-exprlist-count subexprs)
       (vl-scopeexpr-count x))
    :hints (("goal"
             :in-theory (enable vl-scopeexpr-count)))
    :rule-classes :linear))

(define vl-scopeexpr-update-subexprs ((x vl-scopeexpr-p)
                                      (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-scopeexpr->subexprs x)))
  :returns (new-x vl-scopeexpr-p)
  :measure (vl-scopeexpr-count x)
  :verify-guards nil
  (vl-scopeexpr-case x
    :end (change-vl-scopeexpr-end x :hid (vl-hidexpr-update-subexprs x.hid subexprs))
    :colon (change-vl-scopeexpr-colon
            x :first x.first
            :rest (vl-scopeexpr-update-subexprs x.rest subexprs)))
  ///
  (verify-guards vl-scopeexpr-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-scopeexpr->subexprs x))))))
  (defthm vl-scopeexpr-update-subexprs-identity
    (equal (vl-scopeexpr-update-subexprs x (vl-scopeexpr->subexprs x))
           (vl-scopeexpr-fix x))
    :hints(("Goal" :in-theory (enable vl-scopeexpr->subexprs))))

  (defthm vl-scopeexpr-update-subexprs-identity2
    (implies (equal (len y) (len (vl-scopeexpr->subexprs x)))
             (equal (vl-scopeexpr->subexprs (vl-scopeexpr-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-scopeexpr->subexprs)
            :induct t))))

(define vl-range->subexprs ((x vl-range-p))
  :returns (subexprs vl-exprlist-p)
  (b* (((vl-range x)))
    (list x.msb x.lsb))
  ///
  (defret vl-exprlist-count-of-vl-range->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-range-count x))
    :hints (("goal"
             :in-theory (enable vl-range-count)))
    :rule-classes :linear))

(define vl-range-update-subexprs ((x vl-range-p)
                                  (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-range->subexprs x)))
  :returns (new-x vl-range-p)
  :verify-guards nil
  :ignore-ok t
  (change-vl-range
   x
   :msb (car subexprs)
   :lsb (cadr subexprs))
  ///
  (verify-guards vl-range-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-range->subexprs x))))))
  (defthm vl-range-update-subexprs-identity
    (equal (vl-range-update-subexprs x (vl-range->subexprs x))
           (vl-range-fix x))
    :hints(("Goal" :in-theory (enable vl-range->subexprs))))

  (defthm vl-range-update-subexprs-identity2
    (implies (equal (len y) (len (vl-range->subexprs x)))
             (equal (vl-range->subexprs (vl-range-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-range->subexprs)))))

(define vl-plusminus->subexprs ((x vl-plusminus-p))
  :returns (subexprs vl-exprlist-p)
  (b* (((vl-plusminus x)))
    (list x.base x.width))
  ///
  (defret vl-exprlist-count-of-vl-plusminus->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-plusminus-count x))
    :hints (("goal"
             :in-theory (enable vl-plusminus-count)))
    :rule-classes :linear))

(define vl-plusminus-update-subexprs ((x vl-plusminus-p)
                                      (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-plusminus->subexprs x)))
  :returns (new-x vl-plusminus-p)
  :verify-guards nil
  :ignore-ok t
  (change-vl-plusminus
   x
   :base (car subexprs)
   :width (cadr subexprs))
  ///
  (verify-guards vl-plusminus-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-plusminus->subexprs x))))))
  (defthm vl-plusminus-update-subexprs-identity
    (equal (vl-plusminus-update-subexprs x (vl-plusminus->subexprs x))
           (vl-plusminus-fix x))
    :hints(("Goal" :in-theory (enable vl-plusminus->subexprs))))

  (defthm vl-plusminus-update-subexprs-identity2
    (implies (equal (len y) (len (vl-plusminus->subexprs x)))
             (equal (vl-plusminus->subexprs (vl-plusminus-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-plusminus->subexprs)))))


(define vl-partselect->subexprs ((x vl-partselect-p))
  :returns (subexprs vl-exprlist-p)
  (vl-partselect-case x
    :none nil
    :range (vl-range->subexprs x.range)
    :plusminus (vl-plusminus->subexprs x.plusminus))
  ///
  (defret vl-exprlist-count-of-vl-partselect->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-partselect-count x))
    :hints (("goal"
             :in-theory (enable vl-partselect-count)))
    :rule-classes :linear))

(define vl-partselect-update-subexprs ((x vl-partselect-p)
                                      (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-partselect->subexprs x)))
  :returns (new-x vl-partselect-p)
  :verify-guards nil
  (vl-partselect-case x
    :none (vl-partselect-fix x)
    :range (vl-range->partselect (vl-range-update-subexprs x.range subexprs))
    :plusminus (vl-plusminus->partselect (vl-plusminus-update-subexprs x.plusminus subexprs)))
  ///
  (verify-guards vl-partselect-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-partselect->subexprs x))))))
  (defthm vl-partselect-update-subexprs-identity
    (equal (vl-partselect-update-subexprs x (vl-partselect->subexprs x))
           (vl-partselect-fix x))
    :hints(("Goal" :in-theory (enable vl-partselect->subexprs))))

  (defthm vl-partselect-update-subexprs-identity2
    (implies (equal (len y) (len (vl-partselect->subexprs x)))
             (equal (vl-partselect->subexprs (vl-partselect-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-partselect->subexprs)))))

(define vl-arrayrange->subexprs ((x vl-arrayrange-p))
  :returns (subexprs vl-exprlist-p)
  (vl-arrayrange-case x
    :none nil
    :index (list x.expr)
    :range (vl-range->subexprs x.range)
    :plusminus (vl-plusminus->subexprs x.plusminus))
  ///
  (defret vl-exprlist-count-of-vl-arrayrange->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-arrayrange-count x))
    :hints (("goal"
             :in-theory (enable vl-arrayrange-count)))
    :rule-classes :linear))

(define vl-arrayrange-update-subexprs ((x vl-arrayrange-p)
                                       (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-arrayrange->subexprs x)))
  :returns (new-x vl-arrayrange-p)
  :verify-guards nil
  (vl-arrayrange-case x
    :none (vl-arrayrange-fix x)
    :index (vl-expr->arrayrange (car subexprs))
    :range (vl-range->arrayrange (vl-range-update-subexprs x.range subexprs))
    :plusminus (vl-plusminus->arrayrange (vl-plusminus-update-subexprs x.plusminus subexprs)))
  ///
  (verify-guards vl-arrayrange-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-arrayrange->subexprs x))))))
  (defthm vl-arrayrange-update-subexprs-identity
    (equal (vl-arrayrange-update-subexprs x (vl-arrayrange->subexprs x))
           (vl-arrayrange-fix x))
    :hints(("Goal" :in-theory (enable vl-arrayrange->subexprs))))

  (defthm vl-arrayrange-update-subexprs-identity2
    (implies (equal (len y) (len (vl-arrayrange->subexprs x)))
             (equal (vl-arrayrange->subexprs (vl-arrayrange-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-arrayrange->subexprs)))))



(define vl-streamexpr->subexprs ((x vl-streamexpr-p))
  :returns (subexprs vl-exprlist-p)
  (b* (((vl-streamexpr x)))
    (cons x.expr (vl-arrayrange->subexprs x.part)))
  ///
  (defret vl-exprlist-count-of-vl-streamexpr->subexprs
    (< (vl-exprlist-count subexprs)
       (vl-streamexpr-count x))
    :hints (("goal"
             :in-theory (enable vl-streamexpr-count)))
    :rule-classes :linear))


(define vl-streamexpr-update-subexprs ((x vl-streamexpr-p)
                                       (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-streamexpr->subexprs x)))
  :returns (new-x vl-streamexpr-p)
  :verify-guards nil
  (b* (((vl-streamexpr x)))
    (change-vl-streamexpr
     x :expr (car subexprs)
     :part (vl-arrayrange-update-subexprs x.part (cdr subexprs))))
  ///
  (verify-guards vl-streamexpr-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-streamexpr->subexprs x))))))
  (defthm vl-streamexpr-update-subexprs-identity
    (equal (vl-streamexpr-update-subexprs x (vl-streamexpr->subexprs x))
           (vl-streamexpr-fix x))
    :hints(("Goal" :in-theory (enable vl-streamexpr->subexprs))))

  (defthm vl-streamexpr-update-subexprs-identity2
    (implies (equal (len y) (len (vl-streamexpr->subexprs x)))
             (equal (vl-streamexpr->subexprs (vl-streamexpr-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-streamexpr->subexprs)))))


(define vl-streamexprlist->subexprs ((x vl-streamexprlist-p))
  :returns (subexprs vl-exprlist-p)
  (if (atom x)
      nil
    (append (vl-streamexpr->subexprs (car x))
            (vl-streamexprlist->subexprs (cdr x))))
  ///
  (defret vl-exprlist-count-of-vl-streamexprlist->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-streamexprlist-count x))
    :hints (("goal"
             :in-theory (enable vl-streamexprlist-count)))
    :rule-classes :linear))


(define vl-streamexprlist-update-subexprs ((x vl-streamexprlist-p)
                                           (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-streamexprlist->subexprs x)))
  :returns (new-x vl-streamexprlist-p)
  :verify-guards nil
  (if (atom x)
      x
    (let ((len (len (vl-streamexpr->subexprs (car x)))))
      (cons (vl-streamexpr-update-subexprs (car x) (take len subexprs))
            (vl-streamexprlist-update-subexprs (cdr x) (nthcdr len subexprs)))))
  ///
  (verify-guards vl-streamexprlist-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-streamexprlist->subexprs x))))))
  (defthm vl-streamexprlist-update-subexprs-identity
    (equal (vl-streamexprlist-update-subexprs x (vl-streamexprlist->subexprs x))
           (vl-streamexprlist-fix x))
    :hints(("Goal" :in-theory (enable vl-streamexprlist->subexprs))))

  (defthm vl-streamexprlist-update-subexprs-identity2
    (implies (equal (len y) (len (vl-streamexprlist->subexprs x)))
             (equal (vl-streamexprlist->subexprs (vl-streamexprlist-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-streamexprlist->subexprs)))))


(define vl-valuerange->subexprs ((x vl-valuerange-p))
  :returns (subexprs vl-exprlist-p)
  (vl-valuerange-case x
    :valuerange-single (list x.expr)
    :valuerange-range  (list x.low x.high))
  ///
  (defret vl-exprlist-count-of-vl-valuerange->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-valuerange-count x))
    :hints (("goal"
             :in-theory (enable vl-valuerange-count)))
    :rule-classes :linear))

(define vl-valuerange-update-subexprs ((x vl-valuerange-p)
                                      (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-valuerange->subexprs x)))
  :returns (new-x vl-valuerange-p)
  :verify-guards nil
  (vl-valuerange-case x
    :valuerange-single (make-vl-valuerange-single :expr (first subexprs))
    :valuerange-range (make-vl-valuerange-range :low (first subexprs)
                                                :high (second subexprs)))
  ///
  (verify-guards vl-valuerange-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-valuerange->subexprs x))))))
  (defthm vl-valuerange-update-subexprs-identity
    (equal (vl-valuerange-update-subexprs x (vl-valuerange->subexprs x))
           (vl-valuerange-fix x))
    :hints(("Goal" :in-theory (enable vl-valuerange->subexprs))))

  (defthm vl-valuerange-update-subexprs-identity2
    (implies (equal (len y) (len (vl-valuerange->subexprs x)))
             (equal (vl-valuerange->subexprs (vl-valuerange-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-valuerange->subexprs)))))

(define vl-valuerangelist->subexprs ((x vl-valuerangelist-p))
  :returns (subexprs vl-exprlist-p)
  (if (atom x)
      nil
    (append (vl-valuerange->subexprs (car x))
            (vl-valuerangelist->subexprs (cdr x))))
  ///
  (defret vl-exprlist-count-of-vl-valuerangelist->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-valuerangelist-count x))
    :hints (("goal"
             :in-theory (enable vl-valuerangelist-count)))
    :rule-classes :linear))


(define vl-valuerangelist-update-subexprs ((x vl-valuerangelist-p)
                                           (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-valuerangelist->subexprs x)))
  :returns (new-x vl-valuerangelist-p)
  :verify-guards nil
  (if (atom x)
      x
    (let ((len (len (vl-valuerange->subexprs (car x)))))
      (cons (vl-valuerange-update-subexprs (car x) (take len subexprs))
            (vl-valuerangelist-update-subexprs (cdr x) (nthcdr len subexprs)))))
  ///
  (verify-guards vl-valuerangelist-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-valuerangelist->subexprs x))))))
  (defthm vl-valuerangelist-update-subexprs-identity
    (equal (vl-valuerangelist-update-subexprs x (vl-valuerangelist->subexprs x))
           (vl-valuerangelist-fix x))
    :hints(("Goal" :in-theory (enable vl-valuerangelist->subexprs))))

  (defthm vl-valuerangelist-update-subexprs-identity2
    (implies (equal (len y) (len (vl-valuerangelist->subexprs x)))
             (equal (vl-valuerangelist->subexprs (vl-valuerangelist-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-valuerangelist->subexprs)))))


(define vl-patternkey->subexprs ((x vl-patternkey-p))
  :returns (subexprs vl-exprlist-p)
  (vl-patternkey-case x
    :expr (list x.key)
    :otherwise nil)
  ///
  (defret vl-exprlist-count-of-vl-patternkey->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-patternkey-count x))
    :hints (("goal"
             :in-theory (enable vl-patternkey-count)))
    :rule-classes :linear))

(define vl-patternkey-update-subexprs ((x vl-patternkey-p)
                                      (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-patternkey->subexprs x)))
  :returns (new-x vl-patternkey-p)
  :verify-guards nil
  (vl-patternkey-case x
    :expr (change-vl-patternkey-expr x :key (car subexprs))
    :otherwise (vl-patternkey-fix x))
  ///
  (verify-guards vl-patternkey-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-patternkey->subexprs x))))))
  (defthm vl-patternkey-update-subexprs-identity
    (equal (vl-patternkey-update-subexprs x (vl-patternkey->subexprs x))
           (vl-patternkey-fix x))
    :hints(("Goal" :in-theory (enable vl-patternkey->subexprs))))

  (defthm vl-patternkey-update-subexprs-identity2
    (implies (equal (len y) (len (vl-patternkey->subexprs x)))
             (equal (vl-patternkey->subexprs (vl-patternkey-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-patternkey->subexprs)))))

(define vl-slicesize->subexprs ((x vl-slicesize-p))
  :returns (subexprs vl-exprlist-p)
  (vl-slicesize-case x
    :expr (list x.expr)
    :otherwise nil)
  ///
  (defret vl-exprlist-count-of-vl-slicesize->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-slicesize-count x))
    :hints (("goal"
             :in-theory (enable vl-slicesize-count)))
    :rule-classes :linear))

(define vl-slicesize-update-subexprs ((x vl-slicesize-p)
                                      (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-slicesize->subexprs x)))
  :returns (new-x vl-slicesize-p)
  :verify-guards nil
  (vl-slicesize-case x
    :expr (change-vl-slicesize-expr x :expr (car subexprs))
    :otherwise (vl-slicesize-fix x))
  ///
  (verify-guards vl-slicesize-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-slicesize->subexprs x))))))
  (defthm vl-slicesize-update-subexprs-identity
    (equal (vl-slicesize-update-subexprs x (vl-slicesize->subexprs x))
           (vl-slicesize-fix x))
    :hints(("Goal" :in-theory (enable vl-slicesize->subexprs))))

  (defthm vl-slicesize-update-subexprs-identity2
    (implies (equal (len y) (len (vl-slicesize->subexprs x)))
             (equal (vl-slicesize->subexprs (vl-slicesize-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-slicesize->subexprs)))))



(define vl-keyvallist->subexprs ((x vl-keyvallist-p))
  :prepwork ((local (in-theory (disable vl-expr-p-when-vl-maybe-expr-p))))
  :returns (subexprs vl-exprlist-p)
  :measure (vl-keyvallist-count x)
  (b* ((x (vl-keyvallist-fix x)))
    (if (atom x)
        nil
      (append (vl-patternkey->subexprs (caar x))
              (list (cdar x))
              (vl-keyvallist->subexprs (cdr x)))))
  ///
  (defret vl-exprlist-count-of-vl-keyvallist->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-keyvallist-count x))
    :hints (("goal"
             :in-theory (enable vl-keyvallist-count)))
    :rule-classes :linear))


(define vl-keyvallist-update-subexprs ((x vl-keyvallist-p)
                                       (subexprs vl-exprlist-p))
  :prepwork ((local (Defthm vl-expr-p-nth-of-vl-exprlist-p
                      (implies (and (vl-exprlist-p x)
                                    (< (nfix n) (len x)))
                               (vl-expr-p (nth n x)))))
             (local (defthm consp-car-when-vl-keyvallist-p
                      (implies (and (vl-keyvallist-p x)
                                    (consp x))
                               (consp (car x))))))

  :guard (equal (len subexprs)
                (len (vl-keyvallist->subexprs x)))
  :returns (new-x vl-keyvallist-p)
  :measure (vl-keyvallist-count x)
  :verify-guards nil
  (b* ((x (vl-keyvallist-fix x)))
    (if (atom x)
        x
      (let* ((len (len (vl-patternkey->subexprs (caar x))))
             (subexprs (vl-exprlist-fix subexprs)))
        (cons (cons (vl-patternkey-update-subexprs (caar x) (take len subexprs))
                    (vl-expr-fix (car (nthcdr len subexprs))))
              (vl-keyvallist-update-subexprs (cdr x) (nthcdr (+ 1 len) subexprs))))))
  ///
  (verify-guards vl-keyvallist-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-keyvallist->subexprs x))))))
  (defthm vl-keyvallist-update-subexprs-identity
    (equal (vl-keyvallist-update-subexprs x (vl-keyvallist->subexprs x))
           (vl-keyvallist-fix x))
    :hints(("Goal" :in-theory (enable vl-keyvallist->subexprs))))

  (local (defthm cons-nth-cdr-nthcdr
           (implies (< (nfix n) (len x))
                    (equal (cons (nth n x) (cdr (nthcdr n x)))
                           (nthcdr n x)))
           :hints(("Goal" :in-theory (enable nth nthcdr)))))

  (defthm vl-keyvallist-update-subexprs-identity2
    (implies (equal (len y) (len (vl-keyvallist->subexprs x)))
             (equal (vl-keyvallist->subexprs (vl-keyvallist-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (e/d (vl-keyvallist->subexprs)
                                   ((:rewrite nth-of-vl-exprlist-fix)))))))

(define vl-assignpat->subexprs ((x vl-assignpat-p))
  :returns (subexprs vl-exprlist-p)
  (vl-assignpat-case x
    :positional x.vals
    :keyval (vl-keyvallist->subexprs x.pairs)
    :repeat (cons x.reps x.vals))
  ///
  (defret vl-exprlist-count-of-vl-assignpat->subexprs
    (< (vl-exprlist-count subexprs)
       (vl-assignpat-count x))
    :hints (("goal"
             :in-theory (enable vl-assignpat-count)))
    :rule-classes :linear))

(define vl-assignpat-update-subexprs ((x vl-assignpat-p)
                                      (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-assignpat->subexprs x)))
  :returns (new-x vl-assignpat-p)
  :verify-guards nil
  (b* ((subexprs (vl-exprlist-fix subexprs)))
    (vl-assignpat-case x
      :positional (change-vl-assignpat-positional x :vals subexprs)
      :keyval (change-vl-assignpat-keyval
               x :pairs (vl-keyvallist-update-subexprs x.pairs subexprs))
      :repeat (change-vl-assignpat-repeat
               x :reps (car subexprs)
               :vals (cdr subexprs))))
  ///
  (verify-guards vl-assignpat-update-subexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-assignpat->subexprs x))))))
  (defthm vl-assignpat-update-subexprs-identity
    (equal (vl-assignpat-update-subexprs x (vl-assignpat->subexprs x))
           (vl-assignpat-fix x))
    :hints(("Goal" :in-theory (enable vl-assignpat->subexprs))))

  (defthm vl-assignpat-update-subexprs-identity2
    (implies (equal (len y) (len (vl-assignpat->subexprs x)))
             (equal (vl-assignpat->subexprs (vl-assignpat-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-assignpat->subexprs)))))

(define vl-maybe-exprlist->subexprs ((x vl-maybe-exprlist-p))
  :returns (subexprs vl-exprlist-p)
  (if (atom x)
      nil
    (if (car x)
        (cons (vl-expr-fix (car x))
              (vl-maybe-exprlist->subexprs (cdr x)))
      (vl-maybe-exprlist->subexprs (cdr x))))
  ///
  (defret vl-exprlist-count-of-vl-maybe-exprlist->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-maybe-exprlist-count x))
    :hints(("Goal" :in-theory (enable vl-exprlist-count vl-maybe-exprlist-count)))
    :rule-classes :linear))

(define vl-maybe-exprlist-update-subexprs ((x vl-maybe-exprlist-p)
                                           (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-maybe-exprlist->subexprs x)))
  :guard-hints (("goal" :in-theory (enable vl-maybe-exprlist->subexprs)))
  :returns (new-x vl-maybe-exprlist-p)
  (if (atom x)
      nil
    (if (car x)
        (cons (vl-expr-fix (car subexprs))
              (vl-maybe-exprlist-update-subexprs (cdr x) (cdr subexprs)))
      (cons nil (vl-maybe-exprlist-update-subexprs (cdr x) subexprs))))
  ///
  (defthm vl-maybe-exprlist-update-subexprs-identity
    (equal (vl-maybe-exprlist-update-subexprs x (vl-maybe-exprlist->subexprs x))
           (vl-maybe-exprlist-fix x))
    :hints(("Goal" :in-theory (enable vl-maybe-exprlist->subexprs))))

  (defthm vl-maybe-exprlist-update-subexprs-identity2
    (implies (equal (len y) (len (vl-maybe-exprlist->subexprs x)))
             (equal (vl-maybe-exprlist->subexprs (vl-maybe-exprlist-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-maybe-exprlist->subexprs)))))

(define vl-call-namedargs->subexprs ((x vl-call-namedargs-p))
  :returns (subexprs vl-exprlist-p)
  :measure (len (vl-call-namedargs-fix x))
  (b* ((x (vl-call-namedargs-fix x)))
    (if (atom x)
        nil
      (if (cdar x)
          (cons (vl-expr-fix (cdar x))
                (vl-call-namedargs->subexprs (cdr x)))
        (vl-call-namedargs->subexprs (cdr x)))))
  ///
  (defret vl-exprlist-count-of-vl-call-namedargs->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-call-namedargs-count x))
    :hints(("Goal" :in-theory (enable vl-exprlist-count vl-call-namedargs-count)))
    :rule-classes :linear))

(define vl-call-namedargs-update-subexprs ((x vl-call-namedargs-p)
                                           (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-call-namedargs->subexprs x)))
  :guard-hints (("goal" :in-theory (enable vl-call-namedargs->subexprs)))
  :returns (new-x vl-call-namedargs-p)
  :measure (len (vl-call-namedargs-fix x))
  (b* ((x (vl-call-namedargs-fix x)))
    (if (atom x)
        nil
      (if (cdar x)
          (cons (cons (string-fix (caar x)) (vl-expr-fix (car subexprs)))
                (vl-call-namedargs-update-subexprs (cdr x) (cdr subexprs)))
        (cons (car x)
              (vl-call-namedargs-update-subexprs (cdr x) subexprs)))))
  ///
  (defthm vl-call-namedargs-update-subexprs-identity
    (equal (vl-call-namedargs-update-subexprs x (vl-call-namedargs->subexprs x))
           (vl-call-namedargs-fix x))
    :hints(("Goal" :in-theory (enable vl-call-namedargs->subexprs))))

  (defthm vl-call-namedargs-update-subexprs-identity2
    (implies (equal (len y) (len (vl-call-namedargs->subexprs x)))
             (equal (vl-call-namedargs->subexprs (vl-call-namedargs-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-call-namedargs->subexprs)))))


(define vl-evatomlist->subexprs ((x vl-evatomlist-p))
  :returns (subexprs vl-exprlist-p)
  :measure (len (vl-evatomlist-fix x))
  (let ((x (vl-evatomlist-fix x)))
    (if (atom x)
        nil
      (cons (vl-evatom->expr (car x))
            (vl-evatomlist->subexprs (cdr x)))))
  ///
  (defthm len-of-vl-evatomlist->subexprs
    (equal (len (vl-evatomlist->subexprs x))
           (len x)))
  (defret vl-exprlist-count-of-vl-evatomlist->subexprs
    (<= (vl-exprlist-count subexprs)
        (vl-evatomlist-count x))
    :hints(("Goal" :in-theory (enable vl-exprlist-count
                                      vl-evatomlist-count)))
    :rule-classes :linear))

(define vl-evatomlist-update-subexprs ((x        vl-evatomlist-p)
                                       (subexprs vl-exprlist-p))
  :guard (equal (len subexprs)
                (len (vl-evatomlist->subexprs x)))
  :guard-hints (("goal" :in-theory (enable vl-evatomlist->subexprs)))
  :returns (new-x vl-evatomlist-p)
  :measure (len (vl-evatomlist-fix x))
  (b* ((x (vl-evatomlist-fix x)))
    (if (atom x)
        x
      (cons (change-vl-evatom (car x) :expr (car subexprs))
            (vl-evatomlist-update-subexprs (cdr x) (cdr subexprs)))))
  ///
  (defthm len-of-vl-evatomlist-update-subexprs
    (equal (len (vl-evatomlist-update-subexprs x subexprs))
           (len x))
    :hints(("Goal" :induct (len x))))
  (defthm vl-evatomlist-update-subexprs-identity
    (equal (vl-evatomlist-update-subexprs x (vl-evatomlist->subexprs x))
           (vl-evatomlist-fix x))
    :hints(("Goal" :in-theory (enable vl-evatomlist->subexprs))))
  (defthm vl-evatomlist->subexprs-of-vl-evatomlist-update-subexprs
    (implies (equal (len subexprs) (len x))
             (equal (vl-evatomlist->subexprs (vl-evatomlist-update-subexprs x subexprs))
                    (vl-exprlist-fix subexprs)))
    :hints(("Goal"
            :induct (vl-evatomlist-update-subexprs x subexprs)
            :in-theory (enable vl-evatomlist->subexprs)
            :expand (len x)))))


(define vl-expr->subexprs ((x vl-expr-p))
  :returns (subexprs vl-exprlist-p)
  (vl-expr-case x
    :vl-special nil
    :vl-literal nil
    :vl-index (append-without-guard (vl-scopeexpr->subexprs x.scope)
                                    x.indices
                                    (vl-partselect->subexprs x.part))
    :vl-unary (list x.arg)
    :vl-binary (list x.left x.right)
    :vl-qmark (list x.test x.then x.else)
    :vl-mintypmax (list x.min x.typ x.max)
    :vl-concat x.parts
    :vl-multiconcat (cons x.reps x.parts)
    :vl-stream (append (vl-slicesize->subexprs x.size)
                       (vl-streamexprlist->subexprs x.parts))
    :vl-call (append (vl-scopeexpr->subexprs x.name)
                     (vl-maybe-exprlist->subexprs x.plainargs)
                     (vl-call-namedargs->subexprs x.namedargs))
    :vl-cast (vl-casttype-case x.to
               :size (list x.to.size x.expr)
               :otherwise (list x.expr))
    :vl-inside (cons x.elem (vl-valuerangelist->subexprs x.set))
    :vl-tagged (and x.expr (list x.expr))
    :vl-pattern (vl-assignpat->subexprs x.pat)
    :vl-eventexpr (vl-evatomlist->subexprs x.atoms))
  ///
  (defret vl-exprlist-count-of-vl-expr->subexprs
    (< (vl-exprlist-count subexprs)
       (vl-expr-count x))
    :hints (("goal"
             :expand ((vl-expr-count x)
                      (vl-maybe-expr-count (vl-stream->size x)))
             :in-theory (enable vl-maybe-expr-some->val)))
    :rule-classes :linear)

  (local (in-theory (disable cons-equal double-containment)))

  ;; (defthm vl-expr->subexprs-of-vl-expr-update-type
  ;;   (equal (vl-expr->subexprs (vl-expr-update-type x type))
  ;;          (vl-expr->subexprs x))
  ;;   :hints ((and stable-under-simplificationp
  ;;                '(:in-theory (e/d (vl-expr-update-type))))))

  (defthm vl-expr->subexprs-of-vl-expr-update-atts
    (equal (vl-expr->subexprs (vl-expr-update-atts x atts))
           (vl-expr->subexprs x))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (e/d (vl-expr-update-atts)))))))

(define vl-expr-update-subexprs ((x vl-expr-p)
                                 (subexprs vl-exprlist-p))
  :guard (equal (len subexprs) (len (vl-expr->subexprs x)))
  :guard-hints (("goal" :in-theory (enable vl-expr->subexprs)))
  :returns (new-x vl-expr-p)
  (let* ((subexprs (vl-exprlist-fix subexprs)))
    (vl-expr-case x
      :vl-index (b* ((nscopesubs (len (vl-scopeexpr->subexprs x.scope)))
                     (nindices (len x.indices)))
                  (change-vl-index
                   x
                   :scope (vl-scopeexpr-update-subexprs x.scope (take nscopesubs subexprs))
                   :indices (take nindices (nthcdr nscopesubs subexprs))
                   :part (vl-partselect-update-subexprs x.part (nthcdr (+ nindices nscopesubs) subexprs))))
      :vl-unary
      (change-vl-unary x :arg (car subexprs))
      :vl-binary
      (change-vl-binary x :left (car subexprs) :right (cadr subexprs))
      :vl-qmark
      (change-vl-qmark x :test (car subexprs) :then (cadr subexprs) :else (caddr subexprs))
      :vl-mintypmax
      (change-vl-mintypmax x :min (car subexprs) :typ (cadr subexprs) :max (caddr subexprs))
      :vl-concat
      (change-vl-concat x :parts subexprs)
      :vl-multiconcat
      (change-vl-multiconcat x :reps (car subexprs) :parts (cdr subexprs))
      :vl-stream
      (let ((nsizeexprs (len (vl-slicesize->subexprs x.size))))
        (change-vl-stream
         x
         :size (vl-slicesize-update-subexprs x.size (take nsizeexprs subexprs))
         :parts (vl-streamexprlist-update-subexprs x.parts (nthcdr nsizeexprs subexprs))))
      :vl-call
      (let* ((nnameexprs (len (vl-scopeexpr->subexprs x.name)))
             (plainargexprs (len (vl-maybe-exprlist->subexprs x.plainargs))))
        (change-vl-call x :name (vl-scopeexpr-update-subexprs x.name (take nnameexprs subexprs))
                        :plainargs (vl-maybe-exprlist-update-subexprs x.plainargs
                                                                      (take plainargexprs (nthcdr nnameexprs subexprs)))
                        :namedargs (vl-call-namedargs-update-subexprs
                                    x.namedargs (nthcdr (+ nnameexprs plainargexprs) subexprs))))
      :vl-cast
      (vl-casttype-case x.to
        :size (change-vl-cast x :to (change-vl-casttype-size x.to :size (car subexprs))
                              :expr (cadr subexprs))
        :otherwise (change-vl-cast x :expr (car subexprs)))
      :vl-inside
      (change-vl-inside x :elem (car subexprs)
                        :set (vl-valuerangelist-update-subexprs x.set (cdr subexprs)))
      :vl-tagged (if x.expr
                     (change-vl-tagged x :expr (car subexprs))
                   (vl-expr-fix x))
      :vl-pattern
      (change-vl-pattern x :pat (vl-assignpat-update-subexprs x.pat subexprs))
      :vl-eventexpr
      (change-vl-eventexpr x :atoms (vl-evatomlist-update-subexprs x.atoms subexprs))
      :otherwise (vl-expr-fix x)))
  ///
  (defthm vl-expr-update-subexprs-identity
    (equal (vl-expr-update-subexprs x (vl-expr->subexprs x))
           (vl-expr-fix x))
    :hints(("Goal" :in-theory (enable vl-expr->subexprs))))

  ;; (defret vl-expr->type-of-vl-expr-update-subexprs
  ;;   (equal (vl-expr->type new-x)
  ;;          (vl-expr->type x)))

  (defret vl-expr->atts-of-vl-expr-update-subexprs
    (equal (vl-expr->atts new-x)
           (vl-expr->atts x)))

  (defret vl-expr-kind-of-vl-expr-update-subexprs
    (equal (vl-expr-kind new-x)
           (vl-expr-kind x)))

  (local (defthm append-take-nthcdr
           (implies (and (natp n)
                         (natp m)
                         (<= (+ n m) (len x)))
                    (equal (append (take n (nthcdr m x))
                                   (nthcdr (+ n m) x))
                           (nthcdr m x)))
           :hints (("goal" :use ((:instance acl2::append-of-take-and-nthcdr
                                  (acl2::n n) (acl2::x (nthcdr m x))))
                    :in-theory (disable acl2::append-of-take-and-nthcdr)))))

  (local (defthm list-of-car-when-len-1
           (implies (and (vl-exprlist-p x)
                         (equal (len x) 1))
                    (equal (list (car x)) x))
           :hints(("Goal" :in-theory (enable vl-exprlist-p)))))

  (local (defthm car-of-exprlist
           (implies (and (vl-exprlist-p x)
                         (posp (len x)))
                    (car x))))

  (defthm vl-expr-update-subexprs-identity2
    (implies (equal (len y) (len (vl-expr->subexprs x)))
             (equal (vl-expr->subexprs (vl-expr-update-subexprs x y))
                    (vl-exprlist-fix y)))
    :hints(("Goal" :in-theory (enable vl-expr->subexprs)
            :do-not-induct t))))





;; (defines vl-expr-names-nrev
;;   :parents (vl-expr-names)
;;   :flag-local nil
;;   (define vl-expr-names-nrev ((x vl-expr-p) nrev)
;;     :measure (vl-expr-count x)
;;     :flag :expr
;;     (if (vl-fast-atom-p x)
;;         (let ((guts (vl-atom->guts x)))
;;           (if (vl-fast-id-p guts)
;;               (nrev-push (vl-id->name guts) nrev)
;;             (nrev-fix nrev)))
;;       (vl-exprlist-names-nrev (vl-nonatom->args x) nrev)))

;;   (define vl-exprlist-names-nrev ((x vl-exprlist-p) nrev)
;;     :measure (vl-exprlist-count x)
;;     :flag :list
;;     (if (atom x)
;;         (nrev-fix nrev)
;;       (let ((nrev (vl-expr-names-nrev (car x) nrev)))
;;         (vl-exprlist-names-nrev (cdr x) nrev)))))


;; (defines vl-expr-names
;;   :short "Gather the names of all @(see vl-id-p) atoms throughout an
;; expression."

;;   :long "<p>We compute the names of all simple identifiers used throughout an
;; expression.</p>

;; <p>These identifiers might refer to wires, registers, ports, parameters, or
;; anything else in the module.  This function can often be used in conjunction
;; with the @(see allexprs) family of functions, e.g., to see all the wires that
;; are ever mentioned in some module item.</p>

;; <p>Note that we look for @(see vl-id-p) atoms only.  A consequence is that we
;; do not return any hierarchical identifiers, function names, or system function
;; names, since these are not treated as @(see vl-id-p) atoms, but are instead
;; @(see vl-hidpiece-p), @(see vl-sysfunname-p), or @(see vl-funname-p) atoms.</p>

;; <p>Note that as we gather names, we do <b>NOT</b> descend into any embedded
;; @('(* foo = bar *)')-style attributes.</p>

;; <p>@('vl-expr-names') is necessarily mutually-recursive with
;; @('vl-exprlist-names').  For efficiency we use a tail-recursive,
;; accumulator-style functions to do the collection.  Under the hood, we also use
;; @('nreverse') optimization.</p>"

;;   :verify-guards nil
;;   (define vl-expr-names ((x vl-expr-p))
;;     :returns (names string-listp)
;;     :measure (vl-expr-count x)
;;     :flag :expr
;;     (mbe :logic (if (vl-fast-atom-p x)
;;                     (let ((guts (vl-atom->guts x)))
;;                       (if (vl-id-p guts)
;;                           (list (vl-id->name guts))
;;                         nil))
;;                   (vl-exprlist-names (vl-nonatom->args x)))
;;          :exec (with-local-nrev
;;                  (vl-expr-names-nrev x nrev))))

;;   (define vl-exprlist-names ((x vl-exprlist-p))
;;     :returns (names string-listp)
;;     :measure (vl-exprlist-count x)
;;     :flag :list
;;     (mbe :logic (if (consp x)
;;                     (append (vl-expr-names (car x))
;;                             (vl-exprlist-names (cdr x)))
;;                   nil)
;;          :exec (with-local-nrev
;;                  (vl-exprlist-names-nrev x nrev))))
;;   ///
;;   (defthm true-listp-of-vl-expr-names
;;     (true-listp (vl-expr-names x))
;;     :rule-classes :type-prescription)

;;   (defthm true-listp-of-vl-exprlist-names
;;     (true-listp (vl-exprlist-names x))
;;     :rule-classes :type-prescription)

;;   (defthm-vl-expr-names-nrev-flag
;;     (defthm vl-expr-names-nrev-removal
;;       (equal (vl-expr-names-nrev x nrev)
;;              (append nrev (vl-expr-names x)))
;;       :flag :expr)
;;     (defthm vl-exprlist-names-nrev-removal
;;       (equal (vl-exprlist-names-nrev x nrev)
;;              (append nrev (vl-exprlist-names x)))
;;       :flag :list)
;;     :hints(("Goal"
;;             :in-theory (enable acl2::rcons)
;;             :expand ((vl-expr-names-nrev x nrev)
;;                      (vl-exprlist-names-nrev x nrev)
;;                      (vl-expr-names x)
;;                      (vl-exprlist-names x)))))

;;   (verify-guards vl-expr-names)

;;   (defthm vl-exprlist-names-when-atom
;;     (implies (atom x)
;;              (equal (vl-exprlist-names x)
;;                     nil))
;;     :hints(("Goal" :expand (vl-exprlist-names x))))

;;   (defthm vl-exprlist-names-of-cons
;;     (equal (vl-exprlist-names (cons a x))
;;            (append (vl-expr-names a)
;;                    (vl-exprlist-names x)))
;;     :hints(("Goal" :expand ((vl-exprlist-names (cons a x))))))

;;   (defthm vl-exprlist-names-of-append
;;     (equal (vl-exprlist-names (append x y))
;;            (append (vl-exprlist-names x)
;;                    (vl-exprlist-names y)))
;;     :hints(("Goal" :induct (len x))))

;;   (local (defthm c0
;;            (implies (member-equal a x)
;;                     (subsetp-equal (vl-expr-names a)
;;                                    (vl-exprlist-names x)))
;;            :hints(("Goal" :induct (len x)))))

;;   (local (defthm c1
;;            (implies (subsetp-equal x y)
;;                     (subsetp-equal (vl-exprlist-names x)
;;                                    (vl-exprlist-names y)))
;;            :hints(("Goal" :induct (len x)))))

;;   (local (defthm c2
;;            (implies (and (subsetp-equal x y)
;;                          (member-equal a x))
;;                     (subsetp-equal (vl-expr-names a)
;;                                    (vl-exprlist-names y)))))

;;   (defcong set-equiv set-equiv (vl-exprlist-names x) 1
;;     :hints(("Goal" :in-theory (enable set-equiv))))

;;   (deffixequiv-mutual vl-expr-names))



(defines vl-expr-varnames-nrev
  :parents (vl-expr-varnames)
  :flag-local nil
  (define vl-expr-varnames-nrev ((x vl-expr-p) nrev)
    :measure (vl-expr-count x)
    :flag :expr
    (if (vl-idexpr-p x)
        (nrev-push (vl-idexpr->name x) nrev)
      (vl-exprlist-varnames-nrev (vl-expr->subexprs x) nrev)))

  (define vl-exprlist-varnames-nrev ((x vl-exprlist-p) nrev)
    :measure (vl-exprlist-count x)
    :flag :list
    (if (atom x)
        (nrev-fix nrev)
      (let ((nrev (vl-expr-varnames-nrev (car x) nrev)))
        (vl-exprlist-varnames-nrev (cdr x) nrev)))))

(defines vl-expr-varnames
  :verify-guards nil
  (define vl-expr-varnames ((x vl-expr-p))
    :returns (names string-listp)
    :measure (vl-expr-count x)
    :flag :expr
    :short "Extract all the variable names from a VL expression."
    (mbe :logic (if (vl-idexpr-p x)
                    (list (vl-idexpr->name x))
                  (vl-exprlist-varnames (vl-expr->subexprs x)))
         :exec (with-local-nrev
                 (vl-expr-varnames-nrev x nrev))))

  (define vl-exprlist-varnames ((x vl-exprlist-p))
    :returns (names string-listp)
    :measure (vl-exprlist-count x)
    :flag :list
    (mbe :logic (if (consp x)
                    (append (vl-expr-varnames (car x))
                            (vl-exprlist-varnames (cdr x)))
                  nil)
         :exec (if (atom x)
                   nil
                 (with-local-nrev
                   (vl-exprlist-varnames-nrev x nrev)))))
  ///
  (defthm true-listp-of-vl-expr-varnames
    (true-listp (vl-expr-varnames x))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-exprlist-varnames
    (true-listp (vl-exprlist-varnames x))
    :rule-classes :type-prescription)

  (defthm-vl-expr-varnames-nrev-flag
    (defthm vl-expr-varnames-nrev-removal
      (equal (vl-expr-varnames-nrev x nrev)
             (append nrev (vl-expr-varnames x)))
      :flag :expr)
    (defthm vl-exprlist-varnames-nrev-removal
      (equal (vl-exprlist-varnames-nrev x nrev)
             (append nrev (vl-exprlist-varnames x)))
      :flag :list)
    :hints(("Goal"
            :in-theory (enable acl2::rcons)
            :expand ((vl-expr-varnames-nrev x nrev)
                     (vl-exprlist-varnames-nrev x nrev)
                     (vl-expr-varnames x)
                     (vl-exprlist-varnames x)))))

  (verify-guards vl-expr-varnames)

  (defthm vl-exprlist-varnames-when-atom
    (implies (atom x)
             (equal (vl-exprlist-varnames x)
                    nil))
    :hints(("Goal" :expand (vl-exprlist-varnames x))))

  (defthm vl-exprlist-varnames-of-cons
    (equal (vl-exprlist-varnames (cons a x))
           (append (vl-expr-varnames a)
                   (vl-exprlist-varnames x)))
    :hints(("Goal" :expand ((vl-exprlist-varnames (cons a x))))))

  (defthm vl-exprlist-varnames-of-append
    (equal (vl-exprlist-varnames (append x y))
           (append (vl-exprlist-varnames x)
                   (vl-exprlist-varnames y)))
    :hints(("Goal" :induct (len x))))

  (local (defthm c0
           (implies (member-equal a x)
                    (subsetp-equal (vl-expr-varnames a)
                                   (vl-exprlist-varnames x)))
           :hints(("Goal" :induct (len x)))))

  (local (defthm c1
           (implies (subsetp-equal x y)
                    (subsetp-equal (vl-exprlist-varnames x)
                                   (vl-exprlist-varnames y)))
           :hints(("Goal" :induct (len x)))))

  (local (defthm c2
           (implies (and (subsetp-equal x y)
                         (member-equal a x))
                    (subsetp-equal (vl-expr-varnames a)
                                   (vl-exprlist-varnames y)))))

  (defcong set-equiv set-equiv (vl-exprlist-varnames x) 1
    :event-name vl-exprlist-varnames-preserves-set-equiv
    :hints(("Goal" :in-theory (enable set-equiv))))

  (deffixequiv-mutual vl-expr-varnames))



(define vl-op-p (x)
  (or (vl-unaryop-p x)
      (vl-binaryop-p x))
  ///
  (define vl-op-fix ((x vl-op-p))
    :returns (xx vl-op-p)
    (mbe :logic (if (vl-binaryop-p x)
                    x
                  (vl-unaryop-fix x))
         :exec x)
    ///
    (defret vl-op-fix-when-vl-op-p
      (implies (vl-op-p x)
               (equal xx x))))

  (fty::deffixtype vl-op :pred vl-op-p :fix vl-op-fix :equiv vl-op-equiv
    :define t :forward t)

  (defthm vl-op-p-when-unary-or-binary
    (implies (or (vl-unaryop-p x)
                 (vl-binaryop-p x))
             (vl-op-p x))))

(fty::deflist vl-oplist :elt-type vl-op)


(defines vl-expr-ops-nrev
  :parents (vl-expr-ops)
  :flag-local nil
  (define vl-expr-ops-nrev ((x vl-expr-p) nrev)
    :measure (vl-expr-count x)
    :flag :expr
    (b* ((nrev (vl-expr-case x
                 ;; BOZO this doesn't do at all what it used to.  Do we want
                 ;; ops to include things that are their own expression kinds
                 ;; now? e.g. qmark, concat, etc.?
                 :vl-unary (nrev-push x.op nrev)
                 :vl-binary (nrev-push x.op nrev)
                 :otherwise nrev)))
      (vl-exprlist-ops-nrev (vl-expr->subexprs x) nrev)))

  (define vl-exprlist-ops-nrev ((x vl-exprlist-p) nrev)
    :measure (vl-exprlist-count x)
    :flag :list
    (b* (((when (atom x))
          (nrev-fix nrev))
         (nrev (vl-expr-ops-nrev (car x) nrev)))
      (vl-exprlist-ops-nrev (cdr x) nrev))))

(defines vl-expr-ops
  :short "Gather all of the operators used throughout an expression."
  :long "<p>We simply gather all of the unary and binary operators used in the
expression, with repetition.</p>"

  (define vl-expr-ops ((x vl-expr-p))
    :returns (ops vl-oplist-p)
    :measure (vl-expr-count x)
    :verify-guards nil
    :flag :expr
    (mbe :logic (append (vl-expr-case x
                          :vl-unary (list x.op)
                          :vl-binary (list x.op)
                          :otherwise nil)
                        (vl-exprlist-ops (vl-expr->subexprs x)))
         :exec (with-local-nrev
                 (vl-expr-ops-nrev x nrev))))

   (define vl-exprlist-ops ((x vl-exprlist-p))
     :returns (ops vl-oplist-p)
     :measure (vl-exprlist-count x)
     :flag :list
     (mbe :logic (if (consp x)
                     (append (vl-expr-ops (car x))
                             (vl-exprlist-ops (cdr x)))
                   nil)
         :exec (if (atom x)
                   nil
                 (with-local-nrev
                   (vl-exprlist-ops-nrev x nrev)))))
   ///
   (defthm true-listp-of-vl-expr-ops
     (true-listp (vl-expr-ops x))
     :rule-classes :type-prescription)

   (defthm true-listp-of-vl-exprlist-ops
     (true-listp (vl-exprlist-ops x))
     :rule-classes :type-prescription)

   (defthm-vl-expr-ops-nrev-flag
     (defthm vl-expr-ops-nrev-removal
       (equal (vl-expr-ops-nrev x nrev)
              (append nrev (vl-expr-ops x)))
       :flag :expr)
     (defthm vl-exprlist-ops-nrev-removal
       (equal (vl-exprlist-ops-nrev x nrev)
              (append nrev (vl-exprlist-ops x)))
       :flag :list)
     :hints(("Goal"
             :expand ((vl-expr-ops-nrev x nrev)
                      (vl-exprlist-ops-nrev x nrev)
                      (vl-expr-ops x)
                      (vl-exprlist-ops x)))))

   (verify-guards vl-expr-ops)

   (deffixequiv-mutual vl-expr-ops))





(defines vl-expr-has-ops-aux

   (define vl-expr-has-ops-aux ((ops vl-oplist-p)
                                (x   vl-expr-p))
     :guard (true-listp ops)
     :measure (vl-expr-count x)
     (b* ((ops (vl-oplist-fix ops)))
       (or (vl-expr-case x
             :vl-unary (and (member x.op ops) t)
             :vl-binary (and (member x.op ops) t)
             :otherwise nil)
           (vl-exprlist-has-ops-aux ops (vl-expr->subexprs x)))))

   (define vl-exprlist-has-ops-aux ((ops vl-oplist-p)
                                    (x   vl-exprlist-p))
     :guard (true-listp ops)
     :measure (vl-exprlist-count x)
     (if (atom x)
         nil
       (or (vl-expr-has-ops-aux ops (car x))
           (vl-exprlist-has-ops-aux ops (cdr x)))))

   ///

   (defthm-vl-expr-has-ops-aux-flag
     (defthm vl-expr-has-ops-aux-removal
       (equal (vl-expr-has-ops-aux ops x)
              (intersectp-equal (vl-oplist-fix ops) (vl-expr-ops x)))
       :hints ('(:expand ((vl-expr-ops x)
                          (vl-expr-has-ops-aux ops x))))
       :flag vl-expr-has-ops-aux)
     (defthm vl-exprlist-has-ops-aux-removal
       (equal (vl-exprlist-has-ops-aux ops x)
              (intersectp-equal (vl-oplist-fix ops) (vl-exprlist-ops x)))
       :hints ('(:expand ((vl-exprlist-ops x)
                          (vl-exprlist-has-ops-aux ops x))))
       :flag vl-exprlist-has-ops-aux)
     :skip-others t))

(define vl-expr-has-ops ((ops vl-oplist-p)
                         (x   vl-expr-p))
  :enabled t
  (mbe :logic (intersectp-equal (vl-oplist-fix ops) (vl-expr-ops x))
       :exec (vl-expr-has-ops-aux (list-fix ops) x)))

(define vl-exprlist-has-ops ((ops vl-oplist-p)
                             (x   vl-exprlist-p))
  :enabled t
  (mbe :logic (intersectp-equal (vl-oplist-fix ops) (vl-exprlist-ops x))
       :exec (vl-exprlist-has-ops-aux (list-fix ops) x)))


(define vl-zbitlist-p ((x vl-bitlist-p))
  (if (consp x)
      (and (equal (vl-bit-fix (car x)) :vl-zval)
           (vl-zbitlist-p (cdr x)))
    t))

(define vl-zatom-p ((x vl-expr-p))
  (vl-expr-case x
    :vl-literal (vl-value-case x.val
                  :vl-weirdint (vl-zbitlist-p x.val.bits)
                  :vl-extint (vl-bit-equiv x.val.value :vl-zval)
                  :otherwise nil)
    :otherwise nil))





(defines vl-expr-values-nrev
  :parents (vl-expr-values)
  :flag-local nil
  (define vl-expr-values-nrev ((x vl-expr-p) nrev)
    :measure (vl-expr-count x)
    :flag :expr
    (b* ((nrev (vl-expr-case x
                 :vl-literal (nrev-push x.val nrev)
                 :otherwise nrev)))
      (vl-exprlist-values-nrev (vl-expr->subexprs x) nrev)))

  (define vl-exprlist-values-nrev ((x vl-exprlist-p) nrev)
    :measure (vl-exprlist-count x)
    :flag :list
    (if (atom x)
        (nrev-fix nrev)
      (let ((nrev (vl-expr-values-nrev (car x) nrev)))
        (vl-exprlist-values-nrev (cdr x) nrev)))))


(defines vl-expr-values
  :short "Gather all of the values throughout an expression."
  :long "<p>We simply gather all of the values of all of the literals
throughout the expression, with repetition.  The resulting list may contain any
@(see vl-value).</p>"

  (define vl-expr-values ((x vl-expr-p))
    :returns (values vl-valuelist-p)
    :measure (vl-expr-count x)
    :verify-guards nil
    :flag :expr
    (mbe :logic (append (vl-expr-case x
                          :vl-literal (list x.val)
                          :otherwise nil)
                        (vl-exprlist-values (vl-expr->subexprs x)))
         :exec (with-local-nrev (vl-expr-values-nrev x nrev))))

  (define vl-exprlist-values ((x vl-exprlist-p))
    :returns (values vl-valuelist-p)
    :measure (vl-exprlist-count x)
    :flag :list
    (mbe :logic (if (consp x)
                    (append (vl-expr-values (car x))
                            (vl-exprlist-values (cdr x)))
                  nil)
         :exec (if (atom x)
                   nil
                 (with-local-nrev (vl-exprlist-values-nrev x nrev)))))
  ///
  (defthm true-listp-of-vl-expr-values
    (true-listp (vl-expr-values x))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-exprlist-values
    (true-listp (vl-exprlist-values x))
    :rule-classes :type-prescription)

  (defthm-vl-expr-values-nrev-flag
    (defthm vl-expr-values-nrev-removal
      (equal (vl-expr-values-nrev x nrev)
             (append nrev (vl-expr-values x)))
      :flag :expr)
    (defthm vl-exprlist-values-nrev-removal
      (equal (vl-exprlist-values-nrev x nrev)
             (append nrev (vl-exprlist-values x)))
      :flag :list)
    :hints(("Goal"
            :in-theory (enable acl2::rcons)
            :expand ((vl-expr-values-nrev x nrev)
                     (vl-exprlist-values-nrev x nrev)))))

  (verify-guards vl-expr-values)

  (deffixequiv-mutual vl-expr-values))





(defines vl-expr-has-funcalls
  (define vl-expr-has-funcalls ((x vl-expr-p))
    :measure (vl-expr-count x)
    (vl-expr-case x
      :vl-call (not x.systemp)
      :otherwise (vl-exprlist-has-funcalls (vl-expr->subexprs x))))
  (define vl-exprlist-has-funcalls ((x vl-exprlist-p))
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (or (vl-expr-has-funcalls (car x))
          (vl-exprlist-has-funcalls (cdr x))))))



;; (defines vl-expr-selects
;;   :short "Collects up all the selection expressions (bit-selects, part-selects,
;; array indexing, and unresolved indexing) and returns them as a flat list of
;; expressions."
;;   :long "<p>Note: we assume there are no nested selects.</p>"

;;   (define vl-expr-selects ((x vl-expr-p))
;;     :returns (selects vl-exprlist-p)
;;     :measure (vl-expr-count x)
;;     :flag :expr
;;     (b* (((when (vl-fast-atom-p x))
;;           nil)
;;          ((vl-nonatom x) x)
;;          ((when (or (eq x.op :vl-bitselect)
;;                     (eq x.op :vl-partselect-colon)
;;                     (eq x.op :vl-partselect-pluscolon)
;;                     (eq x.op :vl-partselect-minuscolon)
;;                     (eq x.op :vl-index)
;;                     (eq x.op :vl-select-colon)
;;                     (eq x.op :vl-select-pluscolon)
;;                     (eq x.op :vl-select-minuscolon)))
;;           (list (vl-expr-fix x))))
;;       (vl-exprlist-selects x.args)))

;;   (define vl-exprlist-selects ((x vl-exprlist-p))
;;     :returns (selects vl-exprlist-p)
;;     :measure (vl-exprlist-count x)
;;     (if (atom x)
;;         nil
;;       (append (vl-expr-selects (car x))
;;               (vl-exprlist-selects (cdr x)))))
;;   ///
;;   (deffixequiv-mutual vl-expr-selects))


(define vl-bitlist-from-nat ((x     natp)
                             (width natp))
  :returns (bits vl-bitlist-p)
  :short "Turn a natural number into a vl-bitlist-p of the given width."
  (b* (((when (zp width)) nil)
       (width (1- width))
       (bit (if (logbitp width (lnfix x))
                :vl-1val
              :vl-0val)))
    (cons bit (vl-bitlist-from-nat x width)))
  :prepwork ((local (in-theory (disable logbitp))))
  ///
  (defthm len-of-vl-bitlist-from-nat
    (equal (len (vl-bitlist-from-nat x width))
           (nfix width))))



(define vl-expr-add-atts ((new-atts vl-atts-p)
                          (x        vl-expr-p))
  :returns (new-x vl-expr-p)
  (vl-expr-case x
    :vl-special (change-vl-special x :atts (append-without-guard new-atts x.atts))
    :vl-literal (change-vl-literal x :atts (append-without-guard new-atts x.atts))
    :vl-index (change-vl-index x :atts (append-without-guard new-atts x.atts))
    :vl-unary (change-vl-unary x :atts (append-without-guard new-atts x.atts))
    :vl-binary (change-vl-binary x :atts (append-without-guard new-atts x.atts))
    :vl-qmark (change-vl-qmark x :atts (append-without-guard new-atts x.atts))
    :vl-mintypmax (change-vl-mintypmax x :atts (append-without-guard new-atts x.atts))
    :vl-concat (change-vl-concat x :atts (append-without-guard new-atts x.atts))
    :vl-multiconcat (change-vl-multiconcat x :atts (append-without-guard new-atts x.atts))
    :vl-stream (change-vl-stream x :atts (append-without-guard new-atts x.atts))
    :vl-call (change-vl-call x :atts (append-without-guard new-atts x.atts))
    :vl-cast (change-vl-cast x :atts (append-without-guard new-atts x.atts))
    :vl-inside (change-vl-inside x :atts (append-without-guard new-atts x.atts))
    :vl-tagged (change-vl-tagged x :atts (append-without-guard new-atts x.atts))
    :vl-pattern (change-vl-pattern x :atts (append-without-guard new-atts x.atts))
    :vl-eventexpr (change-vl-eventexpr x :atts (append-without-guard new-atts x.atts))))





(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local (defthm simple-loghead-identity
         (implies (and (case-split (< n (expt 2 k)))
                       (natp n)
                       (natp k))
                  (equal (acl2::loghead k n)
                         n))))



(define vl-make-index ((n integerp))
  :short "Safely create a constant integer atom whose value is n."
  :long "<p>The expression we create doesn't have a type, because it would
depend on the context.  In many cases it might suffice to use an integer type;
in this case see @(see vl-make-integer).</p>"
  :returns (index vl-expr-p)
  (let* ((value (lifix n))
         (width (+ 1 (integer-length value))))
    (if (<= width 31)
        ;; Prefer to make indices that look like plain decimal numbers, I
        ;; didn't used to hons these, but now it seems like a good idea since
        ;; the same indicies may be needed frequently.
        (hons-copy
         (make-vl-literal
          :val (make-vl-constint :origwidth 32
                                 :origsign :vl-signed
                                 :wasunsized t
                                 :value (acl2::loghead 32 value))))
      (hons-copy
       (make-vl-literal
        :val (make-vl-constint :origwidth width
                               :origsign :vl-signed
                               :value (acl2::loghead width value))))))
  ///
  (defthm vl-expr-kind-of-vl-make-index
    (eq (vl-expr-kind (vl-make-index n)) :vl-literal))

  (defthm vl-expr-resolved-p-of-vl-make-index
    (vl-expr-resolved-p (vl-make-index n))
    :hints(("Goal" :in-theory (enable vl-expr-resolved-p))))

  (local (defthm logext-of-greater-than-integer-length
           (implies (and (posp n)
                         (< (integer-length x) n))
                    (equal (acl2::logext n x) (ifix x)))
           :hints(("Goal" :in-theory (enable bitops::ihsext-inductions
                                             bitops::ihsext-recursive-redefs)))))


  (defthm vl-resolved->val-of-vl-make-index
    (equal (vl-resolved->val (vl-make-index n))
           (ifix n))
    :hints(("Goal" :in-theory (enable vl-resolved->val))))

  (deffixequiv vl-make-index :args ((n integerp))))


(define vl-make-integer ((n integerp)
                         &key ((bits posp) '32))
  :guard (unsigned-byte-p bits n)
  :short "Safely create a well-typed constant integer atom whose value is n."
  :returns (index vl-expr-p)
  (let* ((value (lnfix n))
         (bits (lposfix bits)))
    (hons-copy
     (make-vl-literal
      :val (make-vl-constint :origwidth bits
                             :origsign :vl-signed
                             :wasunsized t
                             :value (acl2::loghead bits value)))))
  ///
  (defthm vl-expr-kind-of-vl-make-integer
    (eq (vl-expr-kind (vl-make-integer n :bits bits)) :vl-literal))

  (defthm vl-expr-resolved-p-of-vl-make-integer
    (vl-expr-resolved-p (vl-make-integer n :bits bits))
    :hints(("Goal" :in-theory (enable vl-expr-resolved-p))))

  (defthm vl-resolved->val-of-vl-make-integer
    (equal (vl-resolved->val (vl-make-integer n :bits bits))
           (acl2::logext (pos-fix bits) (nfix n)))
    :hints(("Goal" :in-theory (enable vl-resolved->val))))

  (deffixequiv vl-make-integer :args ((n integerp))))




(defxdoc range-tools
  :parents (mlib)
  :short "Basic functions for working with ranges."
  :long "<p>In Verilog, ranges are used in net and register declarations, and
also in module- and gate-instance declarations to describe arrays of modules
or gates.</p>

<p>For gate and module instances, the Verilog-2005 standard is pretty clear.
7.1.5 covers gate instances and 12.1.2 says that module instances have the same
rules.  In short, neither side has to be larger than the other, neither side
has to be zero, and it always specifies abs(left-right)+1 occurrences (so that
if they're the same it means one gate).</p>

<p>BOZO consider \"negative\" numbers and what they might mean.</p>

<p>The specification doesn't give similarly crisp semantics to net and reg
ranges.  Verilog-XL is horribly permissive, allowing even negative indexes and
such.  But Verilog-XL indeed seems to treat w[1:1] as a single bit, and in the
Centaur design there are occurrences of [0:0] and [1:1] and such.  So it may be
that the semantics are supposed to be the same?  It turns out that there are at
least some differences, e.g., you're not allowed to select bit 0 from a plain
wire, but you can select bit 0 from w[0:0], etc.</p>

<p>Historically, VL required the msb index is not smaller than the lsb index.
But we now try to permit designs that use ranges that go from both high to low
and low to high.</p>

<p>The difference is that for a wire like @('wire [5:0] w'), the most
significant bit is @('w[5]') and the least significant is @('w[0]'), whereas
for @('wire [0:5] v'), the most significant bit is @('v[0]') and the least
significant is @('v[5]').</p>

<p>Regardless of how the range is written, the wire behaves the same as far as
operations like addition, concatenation, and so forth are concerned.  This
might seem pretty surprising.  For instance,</p>

@({
wire [3:0] a = 4'b0001;
wire [0:3] b = 4'b1000;
wire [7:0] c = {a, b};
})

<p>Results in @('c') having the value @('8'b 0001_1000').  Basically the way
that the bits of @('b') are represented doesn't affect its value as an integer,
and when we just write @('b') we're referring to that value.</p>

<p>Where it <i>does</i> matter is when bits or parts are selected from the
wire.  That is, @('b[0]') is 1 since its indices go from low to high.</p>")

(local (xdoc::set-default-parents range-tools))

(define vl-range-resolved-p ((x vl-range-p))
  :short "Determine if a range's indices have been resolved to constants."
  :long "<p>Historically we required @('x.msb >= x.lsb'), but now we try to
handle both cases.</p>"
  (b* (((vl-range x) x))
    (and (vl-expr-resolved-p x.msb)
         (vl-expr-resolved-p x.lsb)))
  ///
  (defthm vl-expr-resolved-p-of-vl-range->msb-when-vl-range-resolved-p
    (implies (vl-range-resolved-p x)
             (vl-expr-resolved-p (vl-range->msb x))))

  (defthm vl-expr-resolved-p-of-vl-range->lsb-when-vl-range-resolved-p
    (implies (vl-range-resolved-p x)
             (vl-expr-resolved-p (vl-range->lsb x)))))


(define vl-maybe-range-resolved-p ((x vl-maybe-range-p))
  :inline t
  (or (not x)
      (vl-range-resolved-p x))
  ///
  (defthm vl-maybe-range-resolved-p-when-vl-range-resolved-p
    (implies (vl-range-resolved-p x)
             (vl-maybe-range-resolved-p x)))

  (defthm vl-range-resolved-p-when-vl-maybe-range-resolved-p
    (implies (and (vl-maybe-range-resolved-p x)
                  x)
             (vl-range-resolved-p x))))


;; (define vl-make-n-bit-range ((n posp))
;;   :returns (maybe-range vl-maybe-range-p)
;;   :short "Create the range @('[n-1:0]')."
;;   (let ((n (mbe :logic (pos-fix n) :exec n)))
;;     (make-vl-range :msb (vl-make-index (- n 1))
;;                    :lsb (vl-make-index 0))))

;; (define vl-simpletype-p ((x vl-datatype-p))
;;   (vl-datatype-case x
;;     :vl-coretype
;;     (and (or (eq x.name :vl-reg)
;;              (eq x.name :vl-logic))
;;          (atom x.udims)
;;          (or (atom x.pdims)
;;              (and (atom (cdr x.pdims))
;;                   (mbe :logic (vl-range-p (car x.pdims))
;;                        :exec (not (eq (car x.pdims) :vl-unsized-dimension))))))
;;     :otherwise nil))

;; (define vl-simpletype->range ((x vl-datatype-p))
;;   :guard (vl-simpletype-p x)
;;   :returns (range vl-maybe-range-p)
;;   :guard-hints (("Goal" :in-theory (enable vl-simpletype-p)))
;;   (b* (((vl-coretype x)))
;;     (and (consp x.pdims)
;;          (mbt (vl-range-p (car x.pdims)))
;;          (car x.pdims))))

;; (define vl-simpletype->signedp ((x vl-datatype-p))
;;   :guard (vl-simpletype-p x)
;;   :returns (signedp booleanp :rule-classes :type-prescription)
;;   :guard-hints (("Goal" :in-theory (enable vl-simpletype-p)))
;;   (b* (((vl-coretype x)))
;;     x.signedp))

;; (acl2::def-b*-binder vl-simpletype
;;   :body
;;   (std::da-patbind-fn 'vl-simpletype
;;                       '((range . vl-simpletype->range)
;;                         (signedp . vl-simpletype->signedp))
;;                       acl2::args acl2::forms acl2::rest-expr))


;; (define vl-simplereg-p ((x vl-vardecl-p))
;;   ;; Horrible hack to try to help with porting existing code.
;;   ;;
;;   ;; This will recognize only variables that are either basic reg (or logic)
;;   ;; wires, signed or unsigned, perhaps with a single range, but not with any
;;   ;; more complex dimensions.
;;   (b* (((vl-vardecl x) x))
;;     (and (not x.constp)
;;          (not x.varp)
;;          (not x.lifetime)
;;          (vl-datatype-case x.type :vl-coretype)
;;          (b* (((vl-coretype x.type) x.type))
;;            (and (or (eq x.type.name :vl-reg)
;;                     (eq x.type.name :vl-logic))
;;                 (atom x.type.udims)
;;                 (or (atom x.type.pdims)
;;                     (and (atom (cdr x.type.pdims))
;;                          (mbe :logic (vl-range-p (car x.type.pdims))
;;                               :exec (not (eq (car x.type.pdims) :vl-unsized-dimension))))))))))

;; (deflist vl-simplereglist-p (x)
;;   :guard (vl-vardecllist-p x)
;;   (vl-simplereg-p x))

;; (define vl-simplereg->signedp ((x vl-vardecl-p))
;;   :returns (signedp booleanp :rule-classes :type-prescription)
;;   :guard (vl-simplereg-p x)
;;   :guard-hints (("Goal" :in-theory (enable vl-simplereg-p)))
;;   (b* (((vl-vardecl x) x)
;;        ((vl-coretype x.type) x.type))
;;     x.type.signedp))

;; (define vl-simplereg->range ((x vl-vardecl-p))
;;   :returns (range vl-maybe-range-p)
;;   :guard (vl-simplereg-p x)
;;   :prepwork ((local (in-theory (enable vl-simplereg-p vl-maybe-range-p))))
;;   (b* (((vl-vardecl x) x)
;;        ((vl-coretype x.type) x.type))
;;     (and (consp x.type.pdims)
;;          (vl-range-fix (car x.type.pdims))))
;;   ///
;;   (more-returns
;;    (range (equal (vl-range-p range) (if range t nil))
;;           :name vl-range-p-of-vl-simplereg->range)))

;; (acl2::def-b*-binder vl-simplereg
;;   :body
;;   (std::da-patbind-fn 'vl-simplereg
;;                       '((range . vl-simplereg->range)
;;                         (signedp . vl-simplereg->signedp))
;;                       acl2::args acl2::forms acl2::rest-expr))



;; (define vl-simplenet-p ((x vl-vardecl-p))
;;   ;; Horrible hack to try to help with porting existing code.
;;   ;;
;;   ;; This will recognize only variables that are nets: signed or unsigned, of
;;   ;; any type, perhaps with a single range, but not with any more complex
;;   ;; dimensions.
;;   (b* (((vl-vardecl x) x)
;;        ((unless x.nettype) nil)
;;        ((unless (vl-datatype-case x.type :vl-coretype)) nil)
;;        ((vl-coretype x.type)))
;;     (and (eq x.type.name :vl-logic)
;;          (atom x.type.udims)
;;          (or (atom x.type.pdims)
;;              (and (not (eq (car x.type.pdims) :vl-unsized-dimension))
;;                   (atom (cdr x.type.pdims)))))))

;; (define vl-simplenet->range ((x vl-vardecl-p))
;;   :returns (range vl-maybe-range-p)
;;   :guard (vl-simplenet-p x)
;;   :prepwork ((local (in-theory (enable vl-simplenet-p vl-maybe-range-p))))
;;   (b* (((vl-vardecl x) x)
;;        ((vl-coretype x.type) x.type))
;;     (and (consp x.type.pdims)
;;          (vl-range-fix (car x.type.pdims))))
;;   ///
;;   (more-returns
;;    (range (equal (vl-range-p range) (if range t nil))
;;           :name vl-range-p-of-vl-simplenet->range)))

;; (define vl-simplenet->signedp ((x vl-vardecl-p))
;;   :returns (signedp booleanp :rule-classes :type-prescription)
;;   :guard (vl-simplenet-p x)
;;   :prepwork ((local (in-theory (enable vl-simplenet-p vl-maybe-range-p))))
;;   (b* (((vl-vardecl x) x)
;;        ((vl-coretype x.type) x.type))
;;     x.type.signedp))

;; (define vl-simplenet->nettype ((x vl-vardecl-p))
;;   :returns (nettype vl-nettypename-p)
;;   :guard (vl-simplenet-p x)
;;   :prepwork ((local (in-theory (enable vl-simplenet-p vl-maybe-range-p))))
;;   (b* (((vl-vardecl x) x))
;;     (vl-nettypename-fix x.nettype)))

;; (acl2::def-b*-binder vl-simplenet
;;   :body
;;   (std::da-patbind-fn 'vl-simplenet
;;                       '((range . vl-simplenet->range)
;;                         (signedp . vl-simplenet->signedp)
;;                         (nettype . vl-simplenet->nettype))
;;                       acl2::args acl2::forms acl2::rest-expr))



;; (define vl-simplevar-p ((x vl-vardecl-p))
;;   :returns (bool)
;;   (or (vl-simplenet-p x)
;;       (vl-simplereg-p x))
;;   ///
;;   (defthm vl-simpletype-p-of-simplevar-type
;;     (implies (vl-simplevar-p x)
;;              (vl-simpletype-p (vl-vardecl->type x)))
;;     :hints(("Goal" :in-theory (enable vl-simpletype-p
;;                                       vl-simplevar-p
;;                                       vl-simplenet-p
;;                                       vl-simplereg-p)))))

;; (define vl-simplevar->signedp ((x vl-vardecl-p))
;;   :returns (signedp booleanp :rule-classes :type-prescription)
;;   :guard (vl-simplevar-p x)
;;   :prepwork ((local (in-theory (enable vl-simplevar-p))))
;;   (vl-simpletype->signedp (vl-vardecl->type x)))

;; (define vl-simplevar->range ((x vl-vardecl-p))
;;   :returns (range vl-maybe-range-p)
;;   :guard (vl-simplevar-p x)
;;   :prepwork ((local (in-theory (enable vl-simplevar-p))))
;;   (vl-simpletype->range (vl-vardecl->type x))
;;   ///
;;   (more-returns
;;    (range (equal (vl-range-p range) (if range t nil))
;;           :name vl-range-p-of-vl-simplevar->range)))

;; (acl2::def-b*-binder vl-simplevar
;;   :body
;;   (std::da-patbind-fn 'vl-simplevar
;;                       '((range . vl-simplevar->range)
;;                         (signedp . vl-simplevar->signedp))
;;                       acl2::args acl2::forms acl2::rest-expr))



;; ;; BOZO horrible hack.  For now, we'll make find-net/reg-range only succeed for
;; ;; simple regs, not for other kinds of variables.  Eventually we will want to
;; ;; extend this code to deal with other kinds of variables, but for now, e.g.,
;; ;; we don't want any confusion w.r.t. the range of integers, reals, etc.

;; (define vl-ss-find-range ((name   stringp) (ss vl-scopestack-p))
;;   :returns (mv successp
;;                (maybe-range vl-maybe-range-p))
;;   :enabled t
;;   (b* ((find (vl-scopestack-find-item name ss))
;;        ((unless (and find
;;                      (eq (tag find) :vl-vardecl)
;;                      (vl-simplevar-p find)))
;;         (mv nil nil)))
;;     (mv t (vl-simplevar->range find)))
;;   ///
;;   (more-returns
;;    (maybe-range (iff (vl-range-p maybe-range) maybe-range)
;;                 :name vl-range-p-of-vl-ss-find-range)))

(define vl-range-size ((x vl-range-p))
  :guard (vl-range-resolved-p x)
  :returns (size posp :rule-classes :type-prescription)
  :short "The size of a range is one more than the difference between its msb
and lsb.  For example [3:0] has size 4."
  :long "<p>Notice that this definition still works in the case of [1:1] and so
on.</p>"
  (b* (((vl-range x) x)
       (left  (vl-resolved->val x.msb))
       (right (vl-resolved->val x.lsb)))
    (+ 1 (abs (- left right)))))

(define vl-maybe-range-size ((x vl-maybe-range-p))
  :guard (vl-maybe-range-resolved-p x)
  :returns (size posp :rule-classes :type-prescription)
  :short "Usual way to compute the width of a net/reg, given its range."
  :long "<p>If @('x') is the range of a net declaration or register
declaration, this function returns its width.  That is, if there is a range
then the width of this wire or register is the size of the range.  And
otherwise, it is a single-bit wide.</p>"
  (if (not x)
      1
    (vl-range-size x)))



;; ;; BOZO horrible hack.  For now, we'll make find-net/reg-range only succeed for
;; ;; simple regs, not for other kinds of variables.  Eventually we will want to
;; ;; extend this code to deal with other kinds of variables, but for now, e.g.,
;; ;; we don't want any confusion w.r.t. the range of integers, reals, etc.

;; (define vl-slow-find-net/reg-range ((name stringp)
;;                                     (mod vl-module-p))
;;   :short "Look up the range for a wire or variable declaration."
;;   :returns (mv (successp    booleanp :rule-classes :type-prescription
;;                             "True when @('name') is the name of a wire or variable.")
;;                (maybe-range vl-maybe-range-p
;;                             "The range of the wire, on success."))
;;   :hooks ((:fix :args ((mod vl-module-p))))
;;   (b* ((find (vl-find-vardecl name (vl-module->vardecls mod)))
;;        ((unless (and find
;;                      (vl-simplevar-p find)))
;;         (mv nil nil)))
;;     (mv t (vl-simplevar->range find)))
;;   ///
;;   (more-returns
;;    (maybe-range (equal (vl-range-p maybe-range) (if maybe-range t nil))
;;                 :name vl-range-p-of-vl-slow-find-net/reg-range)))




(defsection random-range-stuff

  (define vl-selwidth ((a natp) (b natp))
    :short "Returns the width of a range @($[a:b]$), i.e., @($|a-b|+1$)."
    :returns (w posp :rule-classes :type-prescription)
    (+ 1 (abs (- (nfix a) (nfix b)))))

  (define vl-range-lsbidx ((x (and (vl-range-p x)
                                   (vl-range-resolved-p x))))
    :short "Extract the LSB (right) index from a resolved @(see vl-range)."
    :returns (lsb integerp :rule-classes :type-prescription)
    (b* (((vl-range x) x))
      (vl-resolved->val x.lsb)))

  (define vl-maybe-range-lsbidx ((x (and (vl-maybe-range-p x)
                                         (vl-maybe-range-resolved-p x))))
    :short "Extract the LSB (right) index from a resolved @(see
            vl-maybe-range); treats the empty range as @('[0:0]'),
            i.e., its LSB index is 0."
    :returns (rsh integerp :rule-classes :type-prescription)
    (b* (((unless x) 0))
      (vl-range-lsbidx x)))

  (define vl-range-msbidx ((x (and (vl-range-p x)
                                   (vl-range-resolved-p x))))
    :short "Extract the MSB (left) index from a resolved @(see vl-range)."
    :returns (msb integerp :rule-classes :type-prescription)
    (b* (((vl-range x) x))
      (vl-resolved->val x.msb)))

  (define vl-maybe-range-msbidx ((x (and (vl-maybe-range-p x)
                                         (vl-maybe-range-resolved-p x))))
    :short "Extract the MSB (left) index from a resolved @(see vl-maybe-range);
            treats the empty range as @('[0:0]'), i.e., its MSB is 0."
    :returns (rsh integerp :rule-classes :type-prescription)
    (b* (((unless x) 0))
      (vl-range-msbidx x)))

  (define vl-range-low-idx ((x (and (vl-range-p x)
                                    (vl-range-resolved-p x))))
    :short "Extract the lesser of the @('msb') and @('lsb') of a resolved @(see
            vl-range)."
    :returns (lowidx integerp :rule-classes :type-prescription)
    (min (vl-range-msbidx x) (vl-range-lsbidx x)))

  (define vl-maybe-range-lowidx ((x (and (vl-range-p x)
                                         (vl-range-resolved-p x))))
    :short "Extract the lesser of the @('msb') and @('lsb') of a resolved @(see
            vl-maybe-range); treats the empty range as @('[0:0]'), i.e., its
            low index is 0."
    :returns (lowidx integerp :rule-classes :type-prescription)
    (if x (vl-range-msbidx x) 0))

  (define vl-range-revp ((x (and (vl-range-p x)
                                 (vl-range-resolved-p x))))
    :short "Determine if a resolved @(see vl-range) is in ``reverse'' order,
            i.e., if its @($msb < lsb$)."
    (< (vl-range-msbidx x) (vl-range-lsbidx x)))

  (define vl-maybe-range-revp ((x (and (vl-maybe-range-p x)
                                       (vl-maybe-range-resolved-p x))))
    :short "Determine if a resolved @(see vl-maybe-range) is in ``reverse''
            order, i.e., if its @($msb < lsb$); treats the empty range as
            @('[0:0]'), i.e., <i>not</i> in reverse order."
    :returns (revp)
    (and x (vl-range-revp x))))




