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
(include-book "../parsetree")
(include-book "expr-tools") ;; bozo for simple delay control stuff
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))

(defxdoc stmt-tools
  :parents (mlib)
  :short "Additional functions for working with statements.")

(local (xdoc::set-default-parents stmt-tools))

(defthm vl-stmtlist-fix-when-atom
  (implies (atom x)
           (equal (vl-stmtlist-fix x)
                  nil))
  :hints(("Goal" :in-theory (enable vl-stmtlist-fix))))

(fty::deflist vl-exprlistlist :elt-type vl-exprlist)

(defsection vl-caselist-p-thms

  (defthm vl-exprlistlist-p-of-alist-keys-when-vl-caselist-p
    (implies (vl-caselist-p x)
             (vl-exprlistlist-p (alist-keys x)))
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
               (cons (cons (vl-exprlist-fix (car x))
                           (vl-stmt-fix (cdr x)))
                     (vl-caselist-fix y))
             (vl-caselist-fix y)))
    :hints(("Goal" :in-theory (enable vl-caselist-fix)))))

  ;; (defthm pairlis$-of-alist-keys-and-alist-vals-when-vl-caselist-p
  ;;   (implies (vl-caselist-p x)
  ;;            (equal (pairlis$ (alist-keys x)
  ;;                             (alist-vals x))
  ;;                   x))
  ;;   :hints(("Goal" :induct (len x))))

  ;; (defthm vl-caselist-p-of-pairlis$-basic
  ;;   (implies (and (vl-exprlist-p exprs)
  ;;                 (vl-stmtlist-p stmts)
  ;;                 (same-lengthp exprs stmts))
  ;;            (vl-caselist-p (pairlis$ exprs stmts)))
  ;;   :hints(("Goal" :in-theory (enable pairlis$))))

  ;; (defthm alist-keys-of-vl-caselist-fix-of-pairlis$
  ;;   (implies (same-lengthp exprs stmts)
  ;;            (equal (alist-keys (vl-caselist-fix (pairlis$ exprs stmts)))
  ;;                   (list-fix (vl-exprlist-fix exprs))))
  ;;   :hints(("Goal" :in-theory (enable pairlis$))))

  ;; (defthm alist-vals-of-vl-caselist-fix-of-pairlis$
  ;;   (implies (same-lengthp exprs stmts)
  ;;            (equal (alist-vals (vl-caselist-fix (pairlis$ exprs stmts)))
  ;;                   (vl-stmtlist-fix stmts)))
  ;;   :hints(("Goal"
  ;;           :induct (pairlis$ exprs stmts)
  ;;           :in-theory (enable pairlis$))))

  ;; (defthm pairlis$-of-vl-exprlist-fix-under-vl-caselist-equiv
  ;;   (vl-caselist-equiv (pairlis$ (vl-exprlist-fix exprs) bodies)
  ;;                      (pairlis$ exprs bodies))
  ;;   :hints(("Goal" :in-theory (enable pairlis$))))

  ;; (defthm pairlis$-of-vl-stmtlist-fix-under-vl-caselist-equiv
  ;;   (vl-caselist-equiv (pairlis$ exprs (vl-stmtlist-fix bodies))
  ;;                      (pairlis$ exprs bodies))
  ;;   :hints(("Goal" :in-theory (enable pairlis$)))))



;; We may not need these anymore ---
;; (defsection vl-stmt-count-thms

;;   (defrule vl-stmt-count-of-cdar-when-vl-caselist-p
;;     (IMPLIES (and (vl-caselist-p x)
;;                   x)
;;              (< (vl-stmt-count (cdar x))
;;                 (vl-caselist-count x)))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defrule vl-stmtlist-count-of-cdr-weak
;;     (<= (vl-stmtlist-count (cdr x))
;;         (vl-stmtlist-count x))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defrule vl-stmtlist-count-of-cdr-strong
;;     (implies (consp x)
;;              (< (vl-stmtlist-count (cdr x))
;;                 (vl-stmtlist-count x)))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defrule vl-caselist-count-of-cdr-weak
;;     (<= (vl-caselist-count (cdr x))
;;         (vl-caselist-count x))
;;     :rule-classes ((:rewrite) (:linear)))

;;   (defrule vl-caselist-count-of-cdr-strong
;;     (implies (and (consp x)
;;                   (vl-caselist-p x))
;;              (< (vl-caselist-count (cdr x))
;;                 (vl-caselist-count x)))
;;     :rule-classes ((:rewrite) (:linear))
;;     :hints(("Goal" :in-theory (enable vl-caselist-count)))))



(define vl-atomicstmt-p
  :short "Recognizer for atomic statements (those with no sub-statements)."
  ((x vl-stmt-p))
  (let ((kind (vl-stmt-kind x)))
    (or (eq kind :vl-nullstmt)
        (eq kind :vl-assignstmt)
        (eq kind :vl-deassignstmt)
        (eq kind :vl-callstmt)
        (eq kind :vl-disablestmt)
        (eq kind :vl-eventtriggerstmt)
        (eq kind :vl-returnstmt)
        (eq kind :vl-breakstmt)
        (eq kind :vl-continuestmt))))

(defthm vl-atomicstmt-forward
  (implies (vl-atomicstmt-p x)
           (let ((kind (vl-stmt-kind x)))
             (or (eq kind :vl-nullstmt)
                 (eq kind :vl-assignstmt)
                 (eq kind :vl-deassignstmt)
                 (eq kind :vl-callstmt)
                 (eq kind :vl-disablestmt)
                 (eq kind :vl-eventtriggerstmt)
                 (eq kind :vl-returnstmt)
                 (eq kind :vl-breakstmt)
                 (eq kind :vl-continuestmt))))
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
    :vl-callstmt         x.atts
    :vl-disablestmt      x.atts
    :vl-eventtriggerstmt x.atts
    :vl-casestmt         x.atts
    :vl-ifstmt           x.atts
    :vl-foreverstmt      x.atts
    :vl-waitstmt         x.atts
    :vl-whilestmt        x.atts
    :vl-dostmt           x.atts
    :vl-forstmt          x.atts
    :vl-foreachstmt      x.atts
    :vl-blockstmt        x.atts
    :vl-repeatstmt       x.atts
    :vl-timingstmt       x.atts
    :vl-breakstmt        x.atts
    :vl-continuestmt     x.atts
    :vl-returnstmt       x.atts
    :vl-assertstmt       x.atts
    :vl-cassertstmt      x.atts))


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
    :vl-casestmt         (cons x.default (alist-vals x.caselist))
    :vl-ifstmt           (list x.truebranch x.falsebranch)
    :vl-foreverstmt      (list x.body)
    :vl-waitstmt         (list x.body)
    :vl-whilestmt        (list x.body)
    :vl-dostmt           (list x.body)
    :vl-forstmt          (append-without-guard
                          x.initassigns x.stepforms (list x.body))
    :vl-foreachstmt      (list x.body)
    :vl-blockstmt        x.stmts
    :vl-repeatstmt       (list x.body)
    :vl-timingstmt       (list x.body)
    :vl-assertstmt       (b* (((vl-assertion x.assertion)))
                           (list x.assertion.success x.assertion.failure))
    :vl-cassertstmt      (b* (((vl-cassertion x.cassertion)))
                           (list x.cassertion.success x.cassertion.failure))
    :otherwise           nil)
  ///
  (local (in-theory (enable vl-stmtlist-count
                            vl-caselist-count
                            vl-stmt-count
                            vl-assertion-count
                            vl-cassertion-count)))

  (local (defthm l0
           (<= (vl-stmtlist-count (alist-vals x))
               (vl-caselist-count x))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal"
                   :induct (len x)
                   :expand ((vl-caselist-count x)
                            (vl-caselist-fix x))))))

  (local (Defthm vl-stmtlist-count-of-append
           (equal (vl-stmtlist-count (append a b))
                  (+ -1 (vl-stmtlist-count a) (vl-stmtlist-count b)))
           :hints(("Goal"
                   :in-theory (enable append)
                   :induct (append a b)
                   :expand ((vl-stmtlist-count a)
                            (:free (a b) (vl-stmtlist-count (cons a b))))))))

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
  :prepwork ((local (defthm vl-exprlist-p-of-flatten-when-vl-exprlistlist-p
                      (implies (vl-exprlistlist-p x)
                               (vl-exprlist-p (flatten x)))
                      :hints(("Goal" :in-theory (enable flatten))))))

  :short "Get all immediate sub-expressions from any compound statement."
  :guard (not (vl-atomicstmt-p x))
  :returns (exprs vl-exprlist-p)
  :long "<p>Note that this only returns the top-level expressions that are
directly part of the statement.</p>"
  (vl-stmt-case x
    :vl-casestmt       (cons x.test (flatten (alist-keys x.caselist)))
    :vl-ifstmt         (list x.condition)
    :vl-foreverstmt    nil
    :vl-waitstmt       (list x.condition)
    :vl-whilestmt      (list x.condition)
    :vl-dostmt         (list x.condition)
    :vl-forstmt        (list x.test)
    :vl-repeatstmt     (list x.condition)
    :vl-blockstmt      nil
    :vl-timingstmt     nil
    :vl-assertstmt     (b* (((vl-assertion x.assertion)))
                         (list x.assertion.condition))
    :vl-cassertstmt    nil ;; bozo?
    :otherwise         nil))


(define vl-compoundstmt->ctrl
  :short "Get the timing control, if any, from an arbitrary compound (non-atomic) statement."
  ((x vl-stmt-p))
  :guard (not (vl-atomicstmt-p x))
  :returns (ctrl vl-maybe-delayoreventcontrol-p)
  :long "<p>This really only makes sense for timing statements.</p>"
  (if (vl-stmt-case x :vl-timingstmt)
      (vl-timingstmt->ctrl x)
    nil)
  ///
  (defthm vl-compoundstmt->ctrl-is-usually-nil
    (implies (not (vl-stmt-case x :vl-timingstmt))
             (equal (vl-compoundstmt->ctrl x)
                    nil))))

(define vl-compoundstmt->vardecls
  :short "Get the declarations, if any, from an arbitrary compound (non-atomic) statement."
  ((x vl-stmt-p))
  :guard (not (vl-atomicstmt-p x))
  :returns (decls vl-vardecllist-p)
  :long "<p>This really only makes sense for block/for statements.</p>"
  (vl-stmt-case x
    :vl-blockstmt   x.vardecls
    :vl-forstmt     x.initdecls
    :vl-foreachstmt x.vardecls
    :otherwise nil)
  ///
  (defthm vl-compoundstmt->vardecls-is-usually-nil
    (implies (and (not (vl-stmt-case x :vl-blockstmt))
                  (not (vl-stmt-case x :vl-forstmt))
                  (not (vl-stmt-case x :vl-foreachstmt)))
             (equal (vl-compoundstmt->vardecls x)
                    nil))))

(define vl-compoundstmt->paramdecls
  :short "Get the declarations, if any, from an arbitrary compound (non-atomic) statement."
  ((x vl-stmt-p))
  :guard (not (vl-atomicstmt-p x))
  :returns (decls vl-paramdecllist-p)
  :long "<p>This really only makes sense for block statements.</p>"
  (vl-stmt-case x
    :vl-blockstmt x.paramdecls
    :otherwise nil)
  ///
  (defthm vl-compoundstmt->paramdecls-is-usually-nil
    (implies (not (vl-stmt-case x :vl-blockstmt))
             (equal (vl-compoundstmt->paramdecls x)
                    nil))))

(define vl-rebuild-caselist ((x         vl-caselist-p)
                             (new-exprs vl-exprlist-p)
                             (new-stmts vl-stmtlist-p))
  :returns (new-x vl-caselist-p)
  :guard (let ((x (vl-caselist-fix x)))
           (and (same-lengthp new-exprs (flatten (alist-keys x)))
                (same-lengthp new-stmts x)))
  :measure (vl-caselist-count x)
  :prepwork ((local (defthm true-listp-when-vl-exprlist-p-rw
                      (implies (vl-exprlist-p x)
                               (true-listp x)))))
  (b* ((x (vl-caselist-fix x))
       ((when (atom x))
        nil)
       ((cons match-exprs ?stmt) (car x))
       (exprs1 (mbe :logic
                    (append (vl-exprlist-fix (first-n (len match-exprs) new-exprs))
                            (acl2::final-cdr (caar x)))
                    :exec
                    (if (true-listp (caar x))
                        (first-n (len match-exprs) new-exprs)
                      (append (first-n (len match-exprs) new-exprs)
                              (acl2::final-cdr (caar x))))))
       (stmt1  (vl-stmt-fix (car new-stmts)))
       (exprs2 (rest-n (len match-exprs) new-exprs)))
    (cons (cons exprs1 stmt1)
          (vl-rebuild-caselist (cdr x) exprs2 (cdr new-stmts))))
  ///
  (local (defthm l1
           (equal (nthcdr (len (car x)) (flatten x))
                  (flatten (cdr x)))))

  (local (defthm l2
           (equal (nthcdr (len (caar x)) (flatten (alist-keys x)))
                  (flatten (alist-keys (cdr x))))))

  (local (defthm l3
           (equal (take (len (car x)) (flatten x))
                  (list-fix (car x)))))

  (local (defthm l4
           (equal (take (len (caar x)) (flatten (alist-keys x)))
                  (list-fix (caar x)))))

  (local (defthm l5
           (implies (vl-caselist-p x)
                    (equal (alist-vals (cdr x))
                           (cdr (alist-vals x))))))

  (local (defthm l6
           (implies (vl-caselist-p x)
                    (equal (car (alist-vals x))
                           (cdar x)))))

  (local (defthm l7
           (implies (vl-caselist-p x)
                    (equal (consp x) (if x t nil)))))

  (local (defthm l8
           (implies (vl-caselist-p x)
                    (equal (consp (car x)) (if x t nil)))))

  (defthm vl-rebuild-caselist-identity
    (implies (vl-caselist-p x)
             (equal (vl-rebuild-caselist x
                                         (flatten (alist-keys x))
                                         (alist-vals x))
                    x))
    :hints(("Goal"
            :do-not '(generalize fertilize eliminate-destructors)
            :in-theory (enable vl-rebuild-caselist))))

  (local (defthm vl-caselist-fix-under-iff
           (implies (vl-caselist-p x)
                    (iff (vl-caselist-fix x)
                         (consp x)))))

  (defthm alist-vals-of-vl-rebuild-caselist
    (implies (and (vl-caselist-p x)
                  (equal (len (alist-keys x)) (len stmts)))
             (equal (alist-vals (vl-rebuild-caselist x exprs stmts))
                    (vl-stmtlist-fix stmts))))

  (local (defthm c0
           (equal (list-fix (nthcdr n x))
                  (nthcdr n (list-fix x)))))

  (local (defthm c1
           (equal (list-fix (vl-exprlist-fix x))
                  (vl-exprlist-fix (list-fix x)))))

  (local (defthm c2
           (implies (<= (nfix n) (len exprs))
                    (equal (vl-exprlist-fix (take n exprs))
                           (take n (vl-exprlist-fix exprs))))))

  (local (in-theory (disable acl2::nthcdr-of-list-fix
                             vl-exprlist-fix-of-list-fix
                             vl-exprlist-fix-of-take)))

  (local (defthmd c3
           (implies (<= (nfix n) (len x))
                    (equal (append (take n x) (nthcdr n (list-fix x)))
                           (list-fix x)))
           :hints (("Goal" :in-theory (enable take)))))

  (local (defthm c4
           (implies (<= (nfix n) (len x))
                    (equal (append (take n (vl-exprlist-fix x))
                                   (nthcdr n (vl-exprlist-fix (list-fix x))))
                           (vl-exprlist-fix (list-fix x))))
           :hints(("Goal" :use ((:instance c3 (x (vl-exprlist-fix x))))))))

  (defthm flatten-of-alist-keys-of-vl-rebuild-caselist
    (implies (and (vl-caselist-p x)
                  (same-lengthp exprs (flatten (alist-keys x))))
             (equal (flatten (alist-keys (vl-rebuild-caselist x exprs stmts)))
                    (vl-exprlist-fix (list-fix exprs))))
    :hints(("Goal" :do-not '(generalize fertilize)))))



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
   (vardecls vl-vardecllist-p "New variable declarations to install.")
   (paramdecls vl-paramdecllist-p "New parameter declarations to install."))
  :guard (and (not (vl-atomicstmt-p x))
              (same-lengthp stmts (vl-compoundstmt->stmts x))
              (same-lengthp exprs (vl-compoundstmt->exprs x))
              (iff ctrl (vl-compoundstmt->ctrl x))
              (or (not vardecls)
                  (member (vl-stmt-kind x) '(:vl-blockstmt :vl-forstmt)))
              (or (not paramdecls)
                  (vl-stmt-case x :vl-blockstmt)))
  :returns (new-x vl-stmt-p)
  :guard-debug t
  :guard-hints(("Goal" :do-not '(generalize fertilize eliminate-destructors)))
  :verbosep t

  :prepwork ((local (in-theory (enable vl-atomicstmt-p
                                       vl-compoundstmt->stmts
                                       vl-compoundstmt->exprs
                                       vl-compoundstmt->ctrl
                                       vl-compoundstmt->vardecls
                                       vl-compoundstmt->paramdecls)))
             (local (defthm l1
                      (implies (vl-caselist-p x)
                               (equal (len (alist-vals x))
                                      (len x)))))

             (local (defthm l2
                      (implies (equal (len x) (+ 1 (len y)))
                               (equal (len (cdr x)) (len y)))))

             (local (in-theory (enable len)))
             (local (defthm vl-timingstmt->ctrl-type
                      (vl-timingstmt->ctrl x)
                      :hints(("Goal" :in-theory (enable (tau-system))))
                      :rule-classes :type-prescription)))

  (let ((x (vl-stmt-fix x)))
    (vl-stmt-case x
      :vl-casestmt
      (change-vl-casestmt x
                          :default (first stmts)
                          :test (first exprs)
                          :caselist (vl-rebuild-caselist x.caselist (rest exprs) (rest stmts)))
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
      :vl-dostmt
      (change-vl-dostmt x
                        :condition (first exprs)
                        :body (first stmts))
      :vl-forstmt
      (b* ((ninitassigns (len x.initassigns))
           (nstepforms   (len x.stepforms))
           (stmts        (vl-stmtlist-fix stmts))
           (stmts-starting-with-stepforms (nthcdr ninitassigns stmts)))
        (change-vl-forstmt x
                           :initdecls vardecls
                           :initassigns (take ninitassigns stmts)
                           :test    (first exprs)
                           :stepforms (take nstepforms stmts-starting-with-stepforms)
                           :body    (nth nstepforms stmts-starting-with-stepforms)))

      :vl-foreachstmt
      (change-vl-foreachstmt x
                             :vardecls vardecls
                             :body (first stmts))

      :vl-repeatstmt
      (change-vl-repeatstmt x
                            :condition (first exprs)
                            :body (first stmts))
      :vl-blockstmt
      (change-vl-blockstmt x
                           :vardecls vardecls
                           :paramdecls paramdecls
                           :stmts stmts)
      :vl-timingstmt
      (change-vl-timingstmt x
                            :ctrl ctrl
                            :body (first stmts))

      :vl-assertstmt
      (change-vl-assertstmt x
                            :assertion (change-vl-assertion x.assertion
                                                            :condition (first exprs)
                                                            :success (first stmts)
                                                            :failure (second stmts)))

      :vl-cassertstmt
      (change-vl-cassertstmt x
                             :cassertion (change-vl-cassertion x.cassertion
                                                               :success (first stmts)
                                                               :failure (second stmts)))

      ;; Atomic statements are ruled out by the guard.
      :vl-nullstmt         (progn$ (impossible) x)
      :vl-assignstmt       (progn$ (impossible) x)
      :vl-deassignstmt     (progn$ (impossible) x)
      :vl-callstmt         (progn$ (impossible) x)
      :vl-disablestmt      (progn$ (impossible) x)
      :vl-breakstmt        (progn$ (impossible) x)
      :vl-continuestmt     (progn$ (impossible) x)
      :vl-returnstmt       (progn$ (impossible) x)
      :vl-eventtriggerstmt (progn$ (impossible) x)))
  ///
  (defthm change-vl-compoundstmt-core-identity
    (equal (change-vl-compoundstmt-core x
                                        (vl-compoundstmt->stmts x)
                                        (vl-compoundstmt->exprs x)
                                        (vl-compoundstmt->ctrl x)
                                        (vl-compoundstmt->vardecls x)
                                        (vl-compoundstmt->paramdecls x))
           (vl-stmt-fix x)))

  (defthm vl-stmtlist-fix-of-take
    (implies (<= (nfix n) (len x))
             (equal (vl-stmtlist-fix (take n x))
                    (take n (vl-stmtlist-fix x))))
    :hints (("Goal" :in-theory (enable take))))

  (defthm vl-stmtlist-fix-of-nthcdr
    (equal (vl-stmtlist-fix (nthcdr n x))
           (nthcdr n (vl-stmtlist-fix x)))
    :hints(("Goal" :in-theory (enable (:i nthcdr))
            :induct (nthcdr n x)
            :expand ((nthcdr n x)))))

  (defthm vl-stmt-fix-of-nth
    (implies (< (nfix n) (len x))
             (equal (vl-stmt-fix (nth n x))
                    (nth n (vl-stmtlist-fix x))))
    :hints(("Goal" :in-theory (enable (:i nth))
            :induct (nth n x)
            :expand ((nth n x)))))

  (defthm vl-compoundstmt->stmts-of-change-vl-compoundstmt-core
    (implies (and (same-lengthp stmts (vl-compoundstmt->stmts x))
                  (same-lengthp exprs (vl-compoundstmt->exprs x)))
             (equal (vl-compoundstmt->stmts (change-vl-compoundstmt-core x stmts exprs ctrl vardecls paramdecls))
                    (vl-stmtlist-fix stmts)))
    :hints ((and stable-under-simplificationp
                 (acl2::equal-by-nths-hint))))

  (defthm vl-compoundstmt->exprs-of-change-vl-compoundstmt-core
    (implies (and (same-lengthp stmts (vl-compoundstmt->stmts x))
                  (same-lengthp exprs (vl-compoundstmt->exprs x)))
             (equal (vl-compoundstmt->exprs (change-vl-compoundstmt-core x stmts exprs ctrl vardecls paramdecls))
                    (list-fix (vl-exprlist-fix exprs)))))

  (defthm vl-compoundstmt->ctrl-of-change-vl-compoundstmt-core
    (implies (iff ctrl (vl-compoundstmt->ctrl x))
             (equal (vl-compoundstmt->ctrl (change-vl-compoundstmt-core x stmts exprs ctrl vardecls paramdecls))
                    (vl-maybe-delayoreventcontrol-fix ctrl)))
    :hints(("Goal" :in-theory (enable vl-maybe-delayoreventcontrol-fix))))

  (defthm vl-compoundstmt->ctrl-of-change-vl-compoundstmt-vardecls
    (implies (or (not vardecls)
                 (vl-stmt-case x :vl-blockstmt)
                 (vl-stmt-case x :vl-forstmt)
                 (vl-stmt-case x :vl-foreachstmt))
             (equal (vl-compoundstmt->vardecls (change-vl-compoundstmt-core x stmts exprs ctrl vardecls paramdecls))
                    (vl-vardecllist-fix vardecls))))

  (defthm vl-compoundstmt->ctrl-of-change-vl-compoundstmt-paramdecls
    (implies (or (not paramdecls)
                 (vl-stmt-case x :vl-blockstmt))
             (equal (vl-compoundstmt->paramdecls (change-vl-compoundstmt-core x stmts exprs ctrl vardecls paramdecls))
                    (vl-paramdecllist-fix paramdecls)))))


(defsection change-vl-compoundstmt
  :parents (stmt-tools)
  :short "Mutate a compound statement."
  :long "<p>General form:</p>
@({
    (change-vl-compoundstmt x
                            [:stmts stmts]
                            [:exprs exprs]
                            [:ctrl ctrl]
                            [:vardecls vardecls]
                            [:paramdecls paramdecls])
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
                (if (assoc :vardecls alist)
                    (cdr (assoc :vardecls alist))
                  (list 'vl-compoundstmt->vardecls x))
                (if (assoc :paramdecls alist)
                    (cdr (assoc :paramdecls alist))
                  (list 'vl-compoundstmt->paramdecls x)))))

  (defmacro change-vl-compoundstmt (x &rest args)
    (change-vl-compoundstmt-fn x
                               (std::da-changer-args-to-alist 'change-vl-compoundstmt
                                                              args
                                                              '(:stmts :exprs :ctrl :vardecls :paramdecls))))

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
                                               (vl-compoundstmt->vardecls x)
                                               (vl-compoundstmt->paramdecls x)))
           :rule-classes nil))

  (local (defthm test2
           (equal (change-vl-compoundstmt x :exprs exprs)
                  (change-vl-compoundstmt-core x
                                               (vl-compoundstmt->stmts x)
                                               exprs
                                               (vl-compoundstmt->ctrl x)
                                               (vl-compoundstmt->vardecls x)
                                               (vl-compoundstmt->paramdecls x)))
           :rule-classes nil))

  (local (defthm test3
           (equal (change-vl-compoundstmt x :exprs exprs :stmts stmts :ctrl ctrl :vardecls vardecls :paramdecls paramdecls)
                  (change-vl-compoundstmt-core x
                                               stmts
                                               exprs
                                               ctrl
                                               vardecls
                                               paramdecls))
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
         (if (atom x)
             nil
           (with-local-nrev (vl-stmtlist-atomicstmts-nrev x nrev)))))

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



(define vl-simpledelaycontrol-p ((x vl-delaycontrol-p))
  :returns bool
  :parents (vl-delaycontrol-p)
  :short "Recognizer for simple delays by some natural-number amount."
  :inline t
  (b* ((val (vl-delaycontrol->value x)))
    (and (vl-expr-resolved-p val)
         (<= 0 (vl-resolved->val val)))))

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
  (vl-stmt-case x :vl-ifstmt))

(define vl-nullstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (vl-stmt-case x :vl-nullstmt))

(define vl-assignstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (vl-stmt-case x :vl-assignstmt))

(define vl-callstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (vl-stmt-case x :vl-callstmt))

;; NOTE: Moved vl-blockstmt-p to parsetree because scopsetack needs it.

(define vl-casestmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (vl-stmt-case x :vl-casestmt))

(define vl-waitstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (vl-stmt-case x :vl-waitstmt))

(define vl-whilestmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (vl-stmt-case x :vl-whilestmt))

(define vl-dostmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (vl-stmt-case x :vl-dostmt))

(define vl-foreverstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (vl-stmt-case x :vl-foreverstmt))

(define vl-repeatstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (vl-stmt-case x :vl-repeatstmt))

(define vl-forstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (vl-stmt-case x :vl-forstmt))

(define vl-timingstmt-p ((x vl-stmt-p))
  :inline t
  :enabled t
  (vl-stmt-case x :vl-timingstmt))
