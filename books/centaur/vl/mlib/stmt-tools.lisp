; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../parsetree")
(include-book "expr-tools") ;; bozo for simple delay control stuff
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc stmt-tools
  :parents (mlib)
  :short "Additional functions for working with statements.")

(local (xdoc::set-default-parents stmt-tools))

(defthm vl-stmtlist-fix-when-atom
  (implies (atom x)
           (equal (vl-stmtlist-fix x)
                  nil))
  :hints(("Goal" :in-theory (enable vl-stmtlist-fix))))


(defsection vl-caselist-p-thms

  (defthm vl-exprlist-p-of-alist-keys-when-vl-caselist-p
    (implies (vl-caselist-p x)
             (vl-exprlist-p (alist-keys x)))
    :hints(("Goal" :induct (len x))))

  (defthm vl-stmtlist-p-of-alist-vals-when-vl-caselist-p
    (implies (vl-caselist-p x)
             (vl-stmtlist-p (alist-vals x)))
    :hints(("Goal" :induct (len x))))

  (defthm vl-caselist-p-when-atom
    (implies (atom x)
             (equal (vl-caselist-p x)
                    (not x)))
    :hints(("Goal" :in-theory (enable vl-caselist-p))))

  (defthm vl-caselist-fix-when-atom
    (implies (atom x)
             (equal (vl-caselist-fix x)
                    nil))
    :hints(("Goal" :in-theory (enable vl-caselist-fix))))

  (defthm vl-caselist-fix-of-cons
    (equal (vl-caselist-fix (cons x y))
           (if (consp x)
               (cons (cons (vl-expr-fix (car x))
                           (vl-stmt-fix (cdr x)))
                     (vl-caselist-fix y))
             (vl-caselist-fix y)))
    :hints(("Goal" :in-theory (enable vl-caselist-fix))))

  (defthm pairlis$-of-alist-keys-and-alist-vals-when-vl-caselist-p
    (implies (vl-caselist-p x)
             (equal (pairlis$ (alist-keys x)
                              (alist-vals x))
                    x))
    :hints(("Goal" :induct (len x))))

  (defthm vl-caselist-p-of-pairlis$-basic
    (implies (and (vl-exprlist-p exprs)
                  (vl-stmtlist-p stmts)
                  (same-lengthp exprs stmts))
             (vl-caselist-p (pairlis$ exprs stmts)))
    :hints(("Goal" :in-theory (enable pairlis$))))

  (defthm alist-keys-of-vl-caselist-fix-of-pairlis$
    (implies (same-lengthp exprs stmts)
             (equal (alist-keys (vl-caselist-fix (pairlis$ exprs stmts)))
                    (list-fix (vl-exprlist-fix exprs))))
    :hints(("Goal" :in-theory (enable pairlis$))))

  (defthm alist-vals-of-vl-caselist-fix-of-pairlis$
    (implies (same-lengthp exprs stmts)
             (equal (alist-vals (vl-caselist-fix (pairlis$ exprs stmts)))
                    (vl-stmtlist-fix stmts)))
    :hints(("Goal"
            :induct (pairlis$ exprs stmts)
            :in-theory (enable pairlis$))))

  (defthm pairlis$-of-vl-exprlist-fix-under-vl-caselist-equiv
    (vl-caselist-equiv (pairlis$ (vl-exprlist-fix exprs) bodies)
                       (pairlis$ exprs bodies))
    :hints(("Goal" :in-theory (enable pairlis$))))

  (defthm pairlis$-of-vl-stmtlist-fix-under-vl-caselist-equiv
    (vl-caselist-equiv (pairlis$ exprs (vl-stmtlist-fix bodies))
                       (pairlis$ exprs bodies))
    :hints(("Goal" :in-theory (enable pairlis$)))))



(defsection vl-stmt-count-thms

  (defrule vl-stmt-count-of-cdar-when-vl-caselist-p
    (IMPLIES (and (vl-caselist-p x)
                  x)
             (< (vl-stmt-count (cdar x))
                (vl-caselist-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defrule vl-stmtlist-count-of-cdr-weak
    (<= (vl-stmtlist-count (cdr x))
        (vl-stmtlist-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defrule vl-stmtlist-count-of-cdr-strong
    (implies (consp x)
             (< (vl-stmtlist-count (cdr x))
                (vl-stmtlist-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defrule vl-caselist-count-of-cdr-weak
    (<= (vl-caselist-count (cdr x))
        (vl-caselist-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defrule vl-caselist-count-of-cdr-strong
    (implies (and (consp x)
                  (vl-caselist-p x))
             (< (vl-caselist-count (cdr x))
                (vl-caselist-count x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable vl-caselist-count)))))



(define vl-atomicstmt-p
  :short "Recognizer for atomic statements (those with no sub-statements)."
  ((x vl-stmt-p))
  (let ((kind (vl-stmt-kind x)))
    (or (eq kind :vl-nullstmt)
        (eq kind :vl-assignstmt)
        (eq kind :vl-deassignstmt)
        (eq kind :vl-enablestmt)
        (eq kind :vl-disablestmt)
        (eq kind :vl-eventtriggerstmt))))

(defthm vl-atomicstmt-forward
  (implies (vl-atomicstmt-p x)
           (let ((kind (vl-stmt-kind x)))
             (or (eq kind :vl-nullstmt)
                 (eq kind :vl-assignstmt)
                 (eq kind :vl-deassignstmt)
                 (eq kind :vl-enablestmt)
                 (eq kind :vl-disablestmt)
                 (eq kind :vl-eventtriggerstmt))))
  :rule-classes :forward-chaining
  :hints(("Goal" :in-theory (enable vl-atomicstmt-p))))

(deflist vl-atomicstmtlist-p (x)
  (vl-atomicstmt-p x)
  :guard (vl-stmtlist-p x)
  ///
  (deffixequiv vl-atomicstmtlist-p :args ((x vl-stmtlist-p))))


(define vl-stmt->atts
  :short "Get the attributes from any statement."
  ((x vl-stmt-p))
  :returns (atts vl-atts-p)
  (vl-stmt-case x
    :vl-nullstmt         x.atts
    :vl-assignstmt       x.atts
    :vl-deassignstmt     x.atts
    :vl-enablestmt       x.atts
    :vl-disablestmt      x.atts
    :vl-eventtriggerstmt x.atts
    :vl-casestmt         x.atts
    :vl-ifstmt           x.atts
    :vl-foreverstmt      x.atts
    :vl-waitstmt         x.atts
    :vl-whilestmt        x.atts
    :vl-forstmt          x.atts
    :vl-blockstmt        x.atts
    :vl-repeatstmt       x.atts
    :vl-timingstmt       x.atts))


(define vl-compoundstmt->stmts
  :short "Get all immediate sub-statements from any compound statement."
  ((x vl-stmt-p))
  :guard (not (vl-atomicstmt-p x))
  :returns (stmts vl-stmtlist-p)
  :long "<p>This is useful for functions that want to recur over statements
without paying much attention to the kinds of statements being traversed.  For
instance, if you just want to collect up all of the expressions everywhere
throughout a statement, you can recur through the @('vl-compoundstmt->stmts')
without having to have separate cases for all the different kinds of
expressions.</p>"
  (vl-stmt-case x
    :vl-casestmt         (cons x.default (alist-vals x.cases))
    :vl-ifstmt           (list x.truebranch x.falsebranch)
    :vl-foreverstmt      (list x.body)
    :vl-waitstmt         (list x.body)
    :vl-whilestmt        (list x.body)
    :vl-forstmt          (list x.body)
    :vl-blockstmt        x.stmts
    :vl-repeatstmt       (list x.body)
    :vl-timingstmt       (list x.body))
  ///
  (local (in-theory (enable vl-stmtlist-count
                            vl-caselist-count
                            vl-stmt-count)))

  (local (defthm l0
           (<= (vl-stmtlist-count (alist-vals x))
               (vl-caselist-count x))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :induct (len x)
                   :expand ((vl-caselist-count x)
                            (vl-caselist-fix x))))))

  (defthm vl-stmtlist-count-of-vl-compoundstmt->stmts-weak
    (<= (vl-stmtlist-count (vl-compoundstmt->stmts x))
        (vl-stmt-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm vl-stmtlist-count-of-vl-compoundstmt->stmts-strong
    (implies (not (vl-atomicstmt-p x))
             (< (vl-stmtlist-count (vl-compoundstmt->stmts x))
                (vl-stmt-count x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable vl-atomicstmt-p)))))


(define vl-compoundstmt->exprs ((x vl-stmt-p))
  :short "Get all immediate sub-expressions from any compound statement."
  :guard (not (vl-atomicstmt-p x))
  :returns (exprs vl-exprlist-p)
  :long "<p>Note that this only returns the top-level expressions that are
directly part of the statement.</p>"
  (vl-stmt-case x
    :vl-casestmt    (cons x.test (alist-keys x.cases))
    :vl-ifstmt      (list x.condition)
    :vl-foreverstmt nil
    :vl-waitstmt    (list x.condition)
    :vl-whilestmt   (list x.condition)
    :vl-forstmt     (list x.initlhs x.initrhs x.test x.nextlhs x.nextrhs)
    :vl-repeatstmt  (list x.condition)
    :vl-blockstmt   nil
    :vl-timingstmt  nil))


(define vl-compoundstmt->ctrl
  :short "Get the timing control, if any, from an arbitrary compound (non-atomic) statement."
  ((x vl-stmt-p))
  :guard (not (vl-atomicstmt-p x))
  :returns (ctrl vl-maybe-delayoreventcontrol-p)
  :long "<p>This really only makes sense for timing statements.</p>"
  (if (eq (vl-stmt-kind x) :vl-timingstmt)
      (vl-timingstmt->ctrl x)
    nil)
  ///
  (defthm vl-compoundstmt->ctrl-is-usually-nil
    (implies (not (eq (vl-stmt-kind x) :vl-timingstmt))
             (equal (vl-compoundstmt->ctrl x)
                    nil))))


(define vl-compoundstmt->decls
  :short "Get the declarations, if any, from an arbitrary compound (non-atomic) statement."
  ((x vl-stmt-p))
  :guard (not (vl-atomicstmt-p x))
  :returns (decls vl-blockitemlist-p)
  :long "<p>This really only makes sense for block statements.</p>"
  (if (eq (vl-stmt-kind x) :vl-blockstmt)
      (vl-blockstmt->decls x)
    nil)
  ///
  (defthm vl-compoundstmt->decls-is-usually-nil
    (implies (not (eq (vl-stmt-kind x) :vl-blockstmt))
             (equal (vl-compoundstmt->decls x)
                    nil))))


(define change-vl-compoundstmt-core
  :parents (change-vl-compoundstmt)
  :short "Mutate an arbitrary compound (non-atomic) statement."
  ((x     vl-stmt-p      "Initial compound statement, to be updated.")
   (stmts vl-stmtlist-p  "New statements to install.  Should agree in length
                          with @(see vl-compoundstmt->stmts).")
   (exprs vl-exprlist-p  "New expressions to install.  Should agree in length
                          with @(see vl-compoundstmt->exprs).")
   (ctrl  vl-maybe-delayoreventcontrol-p "New timing control to install, for
                                          timing statements only.")
   (decls vl-blockitemlist-p "New block item declarations to install."))
  :guard (and (not (vl-atomicstmt-p x))
              (same-lengthp stmts (vl-compoundstmt->stmts x))
              (same-lengthp exprs (vl-compoundstmt->exprs x))
              (iff ctrl (vl-compoundstmt->ctrl x))
              (or (not decls)
                  (eq (vl-stmt-kind x) :vl-blockstmt)))
  :returns (new-x vl-stmt-p)
  :verbosep t
  :prepwork ((local (in-theory (enable vl-atomicstmt-p
                                       vl-compoundstmt->stmts
                                       vl-compoundstmt->exprs
                                       vl-compoundstmt->ctrl
                                       vl-compoundstmt->decls))))
  (let ((x (vl-stmt-fix x)))
    (vl-stmt-case x
      :vl-casestmt
      (change-vl-casestmt x
                          :default (first stmts)
                          :test (first exprs)
                          :cases (pairlis$ (redundant-list-fix (rest exprs))
                                           (rest stmts)))
      :vl-ifstmt
      (change-vl-ifstmt x
                        :condition (first exprs)
                        :truebranch (first stmts)
                        :falsebranch (second stmts))

      :vl-foreverstmt
      (change-vl-foreverstmt x
                             :body (first stmts))

      :vl-waitstmt
      (change-vl-waitstmt x
                          :condition (first exprs)
                          :body (first stmts))
      :vl-whilestmt
      (change-vl-whilestmt x
                           :condition (first exprs)
                           :body (first stmts))
      :vl-forstmt
      (change-vl-forstmt x
                         :initlhs (first exprs)
                         :initrhs (second exprs)
                         :test    (third exprs)
                         :nextlhs (fourth exprs)
                         :nextrhs (fifth exprs)
                         :body    (first stmts))
      :vl-repeatstmt
      (change-vl-repeatstmt x
                            :condition (first exprs)
                            :body (first stmts))
      :vl-blockstmt
      (change-vl-blockstmt x
                           :decls decls
                           :stmts stmts)
      :vl-timingstmt
      (change-vl-timingstmt x
                            :ctrl ctrl
                            :body (first stmts))

      ;; Atomic statements are ruled out by the guard.
      :vl-nullstmt         (progn$ (impossible) x)
      :vl-assignstmt       (progn$ (impossible) x)
      :vl-deassignstmt     (progn$ (impossible) x)
      :vl-enablestmt       (progn$ (impossible) x)
      :vl-disablestmt      (progn$ (impossible) x)
      :vl-eventtriggerstmt (progn$ (impossible) x)))
  ///
  (defthm change-vl-compoundstmt-core-identity
    (equal (change-vl-compoundstmt-core x
                                        (vl-compoundstmt->stmts x)
                                        (vl-compoundstmt->exprs x)
                                        (vl-compoundstmt->ctrl x)
                                        (vl-compoundstmt->decls x))
           (vl-stmt-fix x)))

  (defthm vl-compoundstmt->stmts-of-change-vl-compoundstmt-core
    (implies (and (same-lengthp stmts (vl-compoundstmt->stmts x))
                  (same-lengthp exprs (vl-compoundstmt->exprs x)))
             (equal (vl-compoundstmt->stmts (change-vl-compoundstmt-core x stmts exprs ctrl decls))
                    (vl-stmtlist-fix stmts))))

  (defthm vl-compoundstmt->exprs-of-change-vl-compoundstmt-core
    (implies (and (same-lengthp stmts (vl-compoundstmt->stmts x))
                  (same-lengthp exprs (vl-compoundstmt->exprs x)))
             (equal (vl-compoundstmt->exprs (change-vl-compoundstmt-core x stmts exprs ctrl decls))
                    (list-fix (vl-exprlist-fix exprs)))))

  (defthm vl-compoundstmt->ctrl-of-change-vl-compoundstmt-core
    (implies (iff ctrl (vl-compoundstmt->ctrl x))
             (equal (vl-compoundstmt->ctrl (change-vl-compoundstmt-core x stmts exprs ctrl decls))
                    (vl-maybe-delayoreventcontrol-fix ctrl)))
    :hints(("Goal" :in-theory (enable vl-maybe-delayoreventcontrol-fix))))

  (defthm vl-compoundstmt->ctrl-of-change-vl-compoundstmt-decls
    (implies (or (not decls)
                 (equal (vl-stmt-kind x) :vl-blockstmt))
             (equal (vl-compoundstmt->decls (change-vl-compoundstmt-core x stmts exprs ctrl decls))
                    (vl-blockitemlist-fix decls))))

  ;; Helpers for deffixequiv hooks
  (local (defthm crock
           (equal (vl-caselist-fix (pairlis$ exprs (vl-stmtlist-fix stmts)))
                  (vl-caselist-fix (pairlis$ exprs stmts)))
           :hints(("Goal" :in-theory (enable pairlis$)))))

  (local (defthm crock2
           (equal (vl-caselist-fix (pairlis$ (vl-exprlist-fix exprs) stmts))
                  (vl-caselist-fix (pairlis$ exprs stmts)))
           :hints(("Goal" :in-theory (enable pairlis$))))))


(defsection change-vl-compoundstmt
  :parents (stmt-tools)
  :short "Mutate a compound statement."
  :long "<p>General form:</p>
@({
    (change-vl-compoundstmt x
                            [:stmts stmts]
                            [:exprs exprs]
                            [:ctrl ctrl]
                            [:decls decls])
})

<p>This expands into a suitable call of @(see change-vl-compoundstmt-core).  It
allows you to modify statements without paying much attention to the kind of
statement being modified.</p>

<p>Note that @(see change-vl-compoundstmt-core) has an elaborate guard; e.g.,
you must provide the same number of statements and expressions, and only
provide a :ctrl when there is one, etc.</p>

@(def change-vl-compoundstmt)"

  (defun change-vl-compoundstmt-fn (x alist)
    (declare (xargs :mode :program))
    (cons 'change-vl-compoundstmt-core
          (list x
                (if (assoc :stmts alist)
                    (cdr (assoc :stmts alist))
                  (list 'vl-compoundstmt->stmts x))
                (if (assoc :exprs alist)
                    (cdr (assoc :exprs alist))
                  (list 'vl-compoundstmt->exprs x))
                (if (assoc :ctrl alist)
                    (cdr (assoc :ctrl alist))
                  (list 'vl-compoundstmt->ctrl x))
                (if (assoc :decls alist)
                    (cdr (assoc :decls alist))
                  (list 'vl-compoundstmt->decls x)))))

  (defmacro change-vl-compoundstmt (x &rest args)
    (change-vl-compoundstmt-fn x
                               (std::da-changer-args-to-alist args '(:stmts :exprs :ctrl :decls))))

  (local (defthm test0
           (equal (change-vl-compoundstmt x)
                  (vl-stmt-fix x))
           :rule-classes nil))

  (local (defthm test1
           (equal (change-vl-compoundstmt x :stmts stmts)
                  (change-vl-compoundstmt-core x
                                               stmts
                                               (vl-compoundstmt->exprs x)
                                               (vl-compoundstmt->ctrl x)
                                               (vl-compoundstmt->decls x)
                                               ))
           :rule-classes nil))

  (local (defthm test2
           (equal (change-vl-compoundstmt x :exprs exprs)
                  (change-vl-compoundstmt-core x
                                               (vl-compoundstmt->stmts x)
                                               exprs
                                               (vl-compoundstmt->ctrl x)
                                               (vl-compoundstmt->decls x)
                                               ))
           :rule-classes nil))

  (local (defthm test3
           (equal (change-vl-compoundstmt x :exprs exprs :stmts stmts :ctrl ctrl :decls decls)
                  (change-vl-compoundstmt-core x
                                               stmts
                                               exprs
                                               ctrl
                                               decls))
           :rule-classes nil)))


(defines vl-stmt-atomicstmts-nrev
  :parents (vl-stmt-atomicstmts)
  :flag-local nil
  (define vl-stmt-atomicstmts-nrev ((x vl-stmt-p) nrev)
    :measure (vl-stmt-count x)
    :flag :stmt
    (cond ((vl-atomicstmt-p x)
           (nrev-push (vl-stmt-fix x) nrev))
          (t
           (vl-stmtlist-atomicstmts-nrev (vl-compoundstmt->stmts x) nrev))))

  (define vl-stmtlist-atomicstmts-nrev ((x vl-stmtlist-p) nrev)
    :measure (vl-stmtlist-count x)
    :flag :list
    (if (atom x)
        (nrev-fix nrev)
      (let ((nrev (vl-stmt-atomicstmts-nrev (car x) nrev)))
        (vl-stmtlist-atomicstmts-nrev (cdr x) nrev)))))


(defines vl-stmt-atomicstmts
  :short "@(call vl-stmt-atomicstmts) returns a flat list of all atomic
statements in the statement @('x')."

  :long "<p>This is sometimes useful to avoid needing to write a mutually
recursive function to walk over statements.  For instance, if you want to look
at all of the assignments anywhere within a statement, you can first grab all
of the atomic statements, then filter it down to just the assignments, then
process them.</p>"

  (define vl-stmt-atomicstmts ((x vl-stmt-p))
    :returns (stmts (and (vl-stmtlist-p stmts)
                         (vl-atomicstmtlist-p stmts)))
    :verify-guards nil
    :measure (vl-stmt-count x)
    :flag :stmt
    (mbe :logic
         (cond ((vl-atomicstmt-p x)
                (list (vl-stmt-fix x)))
               (t
                (vl-stmtlist-atomicstmts (vl-compoundstmt->stmts x))))
         :exec
         (with-local-nrev (vl-stmt-atomicstmts-nrev x nrev))))

  (define vl-stmtlist-atomicstmts ((x vl-stmtlist-p))
    :returns (stmts (and (vl-stmtlist-p stmts)
                         (vl-atomicstmtlist-p stmts)))
    :measure (vl-stmtlist-count x)
    :flag :list
    (mbe :logic
         (if (atom x)
             nil
           (append (vl-stmt-atomicstmts (car x))
                   (vl-stmtlist-atomicstmts (cdr x))))
         :exec
         (with-local-nrev (vl-stmtlist-atomicstmts-nrev x nrev))))

  ///
  (defthm-vl-stmt-atomicstmts-nrev-flag
    (defthm vl-stmt-atomicstmts-nrev-removal
      (equal (vl-stmt-atomicstmts-nrev x nrev)
             (append nrev (vl-stmt-atomicstmts x)))
      :flag :stmt)
    (defthm vl-stmtlist-atomicstmts-nrev-removal
      (equal (vl-stmtlist-atomicstmts-nrev x nrev)
             (append nrev (vl-stmtlist-atomicstmts x)))
      :flag :list)
    :hints(("Goal"
            :in-theory (enable acl2::rcons)
            :expand ((vl-stmt-atomicstmts x)
                     (vl-stmtlist-atomicstmts x)
                     (vl-stmt-atomicstmts-nrev x nrev)
                     (vl-stmtlist-atomicstmts-nrev x nrev)))))

  (verify-guards vl-stmt-atomicstmts)

  (deffixequiv-mutual vl-stmt-atomicstmts))


(define vl-filter-blockitems ((x vl-blockitemlist-p))
  :parents (vl-blockitemlist-p)
  :short "Split up blockitems into lists by their type."
  :returns (mv (vardecls vl-vardecllist-p)
               (eventdecls vl-eventdecllist-p)
               (paramdecls vl-paramdecllist-p))
  (b* (((when (atom x))
        (mv nil nil nil))
       ((mv vardecls eventdecls paramdecls)
        (vl-filter-blockitems (cdr x)))
       (x1 (vl-blockitem-fix (car x))))
    (case (tag x1)
      (:vl-vardecl   (mv (cons x1 vardecls) eventdecls paramdecls))
      (:vl-eventdecl (mv vardecls (cons x1 eventdecls) paramdecls))
      (:vl-paramdecl (mv vardecls eventdecls (cons x1 paramdecls)))
      (otherwise
       (progn$ (impossible)
               (mv vardecls eventdecls paramdecls)))))
  ///
  (defmvtypes vl-filter-blockitems
    (true-listp true-listp true-listp)))


(define vl-simpledelaycontrol-p ((x vl-delaycontrol-p))
  :returns bool
  :parents (vl-delaycontrol-p)
  :short "Recognizer for simple delays by some natural-number amount."
  :inline t
  (vl-expr-resolved-p (vl-delaycontrol->value x)))

(define vl-simpledelaycontrol->ticks ((x (and (vl-delaycontrol-p x)
                                              (vl-simpledelaycontrol-p x))))
  :returns (ticks natp :rule-classes :type-prescription)
  :parents (vl-simpledelaycontrol-p)
  :short "Number of ticks for a simple delay, e.g., @('#5') has 5 ticks."
  :guard-hints (("Goal" :in-theory (enable vl-simpledelaycontrol-p)))
  :inline t
  (lnfix (vl-resolved->val (vl-delaycontrol->value x))))






(define vl-ifstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (eq (vl-stmt-kind x) :vl-ifstmt))

(define vl-nullstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (eq (vl-stmt-kind x) :vl-nullstmt))

(define vl-assignstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (eq (vl-stmt-kind x) :vl-assignstmt))

(define vl-enablestmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (eq (vl-stmt-kind x) :vl-enablestmt))

(define vl-blockstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (eq (vl-stmt-kind x) :vl-blockstmt))

(define vl-casestmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (eq (vl-stmt-kind x) :vl-casestmt))

(define vl-waitstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (eq (vl-stmt-kind x) :vl-waitstmt))

(define vl-whilestmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (eq (vl-stmt-kind x) :vl-whilestmt))

(define vl-foreverstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (eq (vl-stmt-kind x) :vl-foreverstmt))

(define vl-repeatstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (eq (vl-stmt-kind x) :vl-repeatstmt))

(define vl-forstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (eq (vl-stmt-kind x) :vl-forstmt))

(define vl-timingstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (eq (vl-stmt-kind x) :vl-timingstmt))



