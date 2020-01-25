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

(include-book "fixtype")
(include-book "std/util/formals" :dir :system)
(include-book "std/lists/mfc-utils" :dir :system)

;; NOTE: If we want to include this in define, obvs we can't have this
;; include-book, but all we really depend on is the DEFGUTS and
;; define-guts-alist definitions.
(include-book "std/util/defines" :dir :system)
(program)
(set-state-ok t)

(defun fixequiv-post-define-hook (guts user-args state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((std::defguts guts) guts))
    (cw "Fixequiv hook: automatic congruences for ~x0.~%" guts.name)
    (value `(deffixequiv ,guts.name . ,user-args))))

;; This doesn't set up any kind of default hook, it just establishes :fix
;; as the name of our hook.
(std::add-post-define-hook :fix fixequiv-post-define-hook)

(defun fixequivs->events (x)
  (if (atom x)
      nil
    (cons (fixequiv-events (car x))
          (fixequivs->events (cdr x)))))

(defun find-formal-by-name (varname formals)
  (if (atom formals)
      nil
    (if (eq (std::formal->name (car formals)) varname)
        (car formals)
      (find-formal-by-name varname (cdr formals)))))

(defconst *deffixequiv-keywords*
  '(:args :omit :hints :verbosep :skip-const-thm :skip-cong-thm))

(defun fixequiv-type-from-guard (guard wrld)
  (and (std::tuplep 2 guard)
       (let ((type1 (car guard)))
         (or (cdr (assoc type1 (table-alist 'fixequiv-guard-type-overrides wrld)))
             type1))))

(defun fixequiv-from-define-formal (fn formal hints opts state)
  (b* (((std::formal fm) formal)
       (type (fixequiv-type-from-guard fm.guard (w state)))
       (stobjname (and (fgetprop fm.name 'acl2::stobj nil (w state))
                       (acl2::congruent-stobj-rep fm.name (w state))))
       (type (or type stobjname))
       ((unless type) nil)
       (formals (fgetprop fn 'acl2::formals :none (w state)))
       (event (deffixequiv-basic-parse (cons fn formals) fm.name type
                `(:skip-ok t :hints ,hints . ,opts) state)))
    (and event (list event))))

(defun fixequivs-from-define-formals (fn omit formals hints opts state)
  (if (atom formals)
      nil
    (append (and (not (member (std::formal->name (car formals)) omit))
                 (fixequiv-from-define-formal fn (car formals) hints opts state))
            (fixequivs-from-define-formals fn omit (cdr formals) hints opts state))))

(defun remove-key (key kwlist)
  (b* ((look (member key kwlist))
       ((unless look) kwlist)
       (pre (take (- (len kwlist) (len look)) kwlist)))
    (append pre (cddr look))))

(defun fixequiv-from-explicit-arg (fn arg gutsformals formals hints global-opts state)
  (b* ((__function__ 'deffixequiv)
       ((mv var type/opts) (if (atom arg) (mv arg nil) (mv (car arg) (cdr arg))))
       ((mv type opts) (if (keywordp (car type/opts))
                           (mv nil type/opts)
                         (mv (car type/opts) (cdr type/opts))))
       (type (or type
                 (b* ((formal (find-formal-by-name var gutsformals))
                      ((unless formal)
                       (if gutsformals
                           (raise "~x0 is not a formal of function ~x1" var fn)
                         (raise "Can't derive argument types from ~x0 because it ~
                        wasn't created with DEFINE." fn)))
                      ((std::formal fm) formal)
                      (type (or (fixequiv-type-from-guard fm.guard (w state))
                                (and (fgetprop fm.name 'acl2::stobj nil (w state))
                                     (acl2::congruent-stobj-rep fm.name (w state)))))
                      ((unless type)
                       (raise "Argument ~x0 of function ~x1 wasn't given a ~
                               (unary) type in its DEFINE declaration" var fn)))
                   type)))
       (arg-hints (cadr (member :hints opts)))
       (opts-without-hints (remove-key :hints opts))
       (opts (append `(:hints ,(append arg-hints hints)) opts-without-hints global-opts)))
    (deffixequiv-basic-parse (cons fn formals)
      var type opts state)))

(defmacro set-fixequiv-guard-override (guard-fn type)
  `(table fixequiv-guard-type-overrides ',guard-fn ',type))

(defun fixequivs-from-explicit-args (fn args gutsformals formals hints global-opts state)
  (if (atom args)
      nil
    (let ((event (fixequiv-from-explicit-arg fn (car args) gutsformals formals hints global-opts  state)))
      (if event
          (cons event
                (fixequivs-from-explicit-args fn (cdr args) gutsformals formals hints global-opts state))
        (fixequivs-from-explicit-args fn (cdr args) gutsformals formals hints global-opts state)))))

(defun deffixequiv-expand-hint-fn (fn stable-under-simplificationp id clause world)
  (b* ((forcing-roundp (not (eql 0 (acl2::access acl2::clause-id id :forcing-round))))
       ((when forcing-roundp) nil)
       (pool-lst (acl2::access acl2::clause-id id :pool-lst))
       (top-levelp (not pool-lst))
       (single-inductionp (equal pool-lst '(1)))
       ((unless (or top-levelp single-inductionp))
        nil)
       ((when (and top-levelp (acl2::recursivep fn t world)))
        `(:computed-hint-replacement t
          :induct (,fn . ,(fgetprop fn 'acl2::formals t world))))
       ((unless stable-under-simplificationp)
        nil)
       (concl (car (last clause)))
       (hint
        (b* (((when (and (consp concl)
                         (eq (car concl) 'not)
                         (consp (second concl))
                         (eq (car (second concl)) fn)))
              (list :expand (list (second concl))))
             ((unless (and (consp concl)
                           (eq (car concl) 'equal)))
              nil)
             (lhs (second concl))
             (rhs (third concl))
             (lhs-hint (if (and (consp lhs)
                                (eq (car lhs) fn))
                           (list lhs)
                         nil))
             (rhs-hint (if (and (consp rhs)
                                (eq (car rhs) fn))
                           (list rhs)
                         nil))
             ((unless (or lhs-hint rhs-hint))
              nil))
          (list :expand (append lhs-hint rhs-hint))))
       ((unless hint)
        nil))
    (observation-cw 'deffixequiv "Giving expand hint ~x0.~%" hint)
    hint))

(defmacro deffixequiv-expand-hint (fn)
  `(deffixequiv-expand-hint-fn ',fn stable-under-simplificationp id clause world))

(defun deffixequiv-default-hints (fnname world)
  (let ((entry (cdr (assoc 'deffixequiv (table-alist 'std::default-hints-table world)))))
    (subst fnname 'fnname entry)))

(defmacro set-deffixequiv-default-hints (hint)
  `(table std::default-hints-table 'deffixequiv ',hint))

(set-deffixequiv-default-hints
 ((deffixequiv-expand-hint fnname)))


(defun deffixequiv-fn (fn kw-args state)
  (b* ((__function__ 'deffixequiv)
       (world (w state))
       ((mv kwd-alist rest)
        (extract-keywords 'deffixequiv *deffixequiv-keywords* kw-args nil))
       ((when rest) (raise "Error: extra arguments: ~x0" rest))

       (guts-alist (std::get-define-guts-alist world))
       (guts (cdr (assoc fn guts-alist)))
       ;; It might be an error if there's no define table entry, but it doesn't
       ;; need to be if the arg types are given explicitly.
       (gutsformals (and guts (std::defguts->formals guts)))
       (args (cdr (assoc :args kwd-alist)))
       (hints (if (assoc :hints kwd-alist)
                  (cdr (assoc :hints kwd-alist))
                (deffixequiv-default-hints fn world)))
       ((when (and (not args) (not guts)))
        (raise "Deffixequiv requires either explicit types for the arguments ~
                to be considered, or for the function to have DEFINE info, ~
                which ~x0 does not." fn))
       (fn (if guts (std::defguts->name-fn guts) fn))
       (omit (cdr (assoc :omit kwd-alist)))
       (global-opts `(:skip-const-thm  ,(cdr (assoc :skip-const-thm kwd-alist))
                      :skip-cong-thm ,(cdr (assoc :skip-cong-thm kwd-alist))))
       ((when (and args omit))
        (raise "Why would you provide both :args and :omit?")))
    (if args
        (fixequivs-from-explicit-args
         fn args gutsformals
         (fgetprop fn 'acl2::formals :none (w state)) hints global-opts state)
      (fixequivs-from-define-formals fn omit gutsformals hints global-opts state))))

(defmacro deffixequiv (fn &rest keys)
  (b* ((verbosep (let ((lst (member :verbosep keys)))
                   (and lst (cadr lst)))))
    `(with-output ,@(and (not verbosep) '(:off :all)) :stack :push
       (make-event
        (cons 'progn
              (fixequivs->events
               (deffixequiv-fn ',fn ',keys state)))))))


(defconst *deffixequiv-mutual-keywords*
  '(:args :omit :verbosep :hints :no-induction-hint))


(defun find-define-guts-by-fn/flag-name (fn gutslist)
  (if (atom gutslist)
      nil
    (if (or (eq fn (std::defguts->name (car gutslist)))
            (eq fn (std::defguts->name-fn (car gutslist)))
            (eq fn (cdr (assoc :flag (std::defguts->kwd-alist (car gutslist))))))
        (car gutslist)
      (find-define-guts-by-fn/flag-name fn (cdr gutslist)))))

(defun find-entry-by-fn/flag-name (guts al)
  (b* (((std::defguts guts) guts))
    (or (assoc guts.name al)
        (assoc guts.name-fn al)
        (assoc (cdr (assoc :flag guts.kwd-alist)) al))))

(defun args->varnames (args)
  (if (atom args)
      nil
    (cons (if (atom (car args)) (car args) (caar args))
          (args->varnames (cdr args)))))

(defun keep-args (args keep-names)
  (if (atom args)
      nil
    (if (member (if (atom (car args)) (car args) (caar args)) keep-names)
        (cons (car args) (keep-args (cdr args) keep-names))
      (keep-args (cdr args) keep-names))))


(defun mutual-fixequivs-from-explicit-args (fn-args univ-args gutslist state)
  (b* (((when (atom gutslist)) nil)
       (guts (car gutslist))
       ((std::defguts guts) guts)
       (formal-names (std::formallist->names guts.formals))
       (fn-fn-args (cdr (find-entry-by-fn/flag-name guts fn-args)))
       ;; We include an arg from the univ-args if
       ;; (1) it is among the function's formals and
       ;; (2) it is not overridden in the fn-args.
       (fn-univ-args (keep-args univ-args
                                (set-difference-eq formal-names
                                                   (args->varnames fn-fn-args))))
       (args (append fn-fn-args fn-univ-args))
       (fixequivs (fixequivs-from-explicit-args
                   guts.name-fn args guts.formals formal-names nil nil state)))
    (cons (cons guts.name fixequivs)
          (mutual-fixequivs-from-explicit-args fn-args univ-args (cdr gutslist) state))))


(defun mutual-fixequivs-from-defines (fn-omit univ-omit gutslist state)
  (b* (((when (atom gutslist)) nil)
       ((std::defguts guts) (car gutslist))
       (omit-look (or (assoc guts.name fn-omit)
                      (assoc guts.name-fn fn-omit)
                      (assoc (cdr (assoc :flag guts.kwd-alist)) fn-omit)))
       (fixequivs (fixequivs-from-define-formals
                   guts.name-fn (append univ-omit (cdr omit-look))
                   guts.formals nil nil state)))
    (cons (cons guts.name fixequivs)
          (mutual-fixequivs-from-defines fn-omit univ-omit (cdr gutslist) state))))

(defun fixequivs->fix-thms-with-flags (flag fixequivs)
  (if (atom fixequivs)
      nil
    (cons (append (fixequiv->fix-thm (car fixequivs)) `(:flag ,flag))
          (fixequivs->fix-thms-with-flags flag (cdr fixequivs)))))

(defun fn-mutual-fixequivs->inductive-fix-thms (fn fixequivs gutslist)
  (b* ((guts (find-define-guts-by-fn/flag-name fn gutslist))
       ((unless guts) (er hard? 'deffixequiv-mutual "function name not found?"))
       (flag (std::guts->flag guts)))
    (fixequivs->fix-thms-with-flags flag fixequivs)))


(defun mutual-fixequivs->inductive-fix-thms (fixequiv-al gutslist)
  (if (atom fixequiv-al)
      nil
    (append (fn-mutual-fixequivs->inductive-fix-thms
             (caar fixequiv-al) (cdar fixequiv-al) gutslist)
            (mutual-fixequivs->inductive-fix-thms (cdr fixequiv-al) gutslist))))

(defun defgutslist->names (x)
  (if (atom x)
      nil
    (cons (std::defguts->name (car x))
          (defgutslist->names (cdr x)))))


(defun deffixequiv-mutual-default-default-hint (fnname id world)
  (let ((fns (acl2::recursivep fnname t world)))
    (and (eql 0 (acl2::access acl2::clause-id id :forcing-round))
         (equal '(1) (acl2::access acl2::clause-id id :pool-lst))
         `(:computed-hint-replacement
           ((and stable-under-simplificationp
                 (std::expand-calls . ,fns)))
           :in-theory (disable . ,fns)))))

(defun deffixequiv-mutual-default-hints (fnname world)
  (let ((entry (cdr (assoc 'deffixequiv-mutual (table-alist 'std::default-hints-table world)))))
    (subst fnname 'fnname entry)))

(defmacro set-deffixequiv-mutual-default-hints (hint)
  `(table std::default-hints-table 'deffixequiv-mutual ',hint))

(set-deffixequiv-mutual-default-hints
 ((deffixequiv-mutual-default-default-hint 'fnname id world)))




(defun mutual-fixequivs->fix-thm (fixequiv-al defines-entry kwd-alist world)
  (b* ((thm-macro (std::defines-guts->flag-defthm-macro defines-entry))
       (gutslist (std::defines-guts->gutslist defines-entry))
       (fn1 (std::defguts->name-fn (car gutslist)))
       (hints-look (assoc :hints kwd-alist))
       (hints (if hints-look
                  (cdr hints-look)
                (deffixequiv-mutual-default-hints fn1 world))))
    `(with-output :stack :pop
       (,thm-macro
        ,@(mutual-fixequivs->inductive-fix-thms
           fixequiv-al gutslist)
        :hints ,hints
        :no-induction-hint ,(cdr (assoc :no-induction-hint kwd-alist))
        :skip-others t))))

(defun fixequivs->const/cong-thms (fixequivs)
  (if (atom fixequivs)
      nil
    (let* ((rest (fixequivs->const/cong-thms (cdr fixequivs)))
           (cong-thm (fixequiv->cong-thm (car fixequivs)))
           (const-thm (fixequiv->const-thm (car fixequivs)))
           (events (cons cong-thm rest)))
      (if const-thm
          (cons const-thm events)
        events))))

(defun mutual-fixequivs->const/cong-thms (fixequiv-al)
  (if (atom fixequiv-al)
      nil
    (append (fixequivs->const/cong-thms (cdar fixequiv-al))
            (mutual-fixequivs->const/cong-thms (cdr fixequiv-al)))))

(defun get-atoms (x)
  (if (atom x)
      nil
    (if (atom (car x))
        (cons (car x) (get-atoms (cdr x)))
      (get-atoms (cdr x)))))

(defun get-conses (x)
  (if (atom x)
      nil
    (if (atom (car x))
        (get-conses (cdr x))
      (cons (car x) (get-conses (cdr x))))))

(defun get-fn-args (args gutslist)
  (if (atom args)
      nil
    (if (and (consp (car args))
             (find-define-guts-by-fn/flag-name (caar args) gutslist))
        (cons (car args) (get-fn-args (cdr args) gutslist))
      (get-fn-args (cdr args) gutslist))))

(defun get-nonfn-args (args gutslist)
  (if (atom args)
      nil
    (if (and (consp (car args))
             (find-define-guts-by-fn/flag-name (caar args) gutslist))
        (get-nonfn-args (cdr args) gutslist)
      (cons (car args) (get-nonfn-args (cdr args) gutslist)))))

(defun deffixequiv-mutual-fn (name kw-args state)
  (b* ((__function__ 'deffixequiv-mutual)
       (world (w state))
       ((mv kwd-alist rest)
        (extract-keywords 'deffixequiv-mutual *deffixequiv-mutual-keywords* kw-args nil))
       ((when rest) (raise "Error: extra arguments: ~x0" rest))
       (defines-alist (std::get-defines-alist world))
       (defines-entry (cdr (assoc name defines-alist)))
       ((unless (and defines-entry
                     (std::defines-guts->flag-defthm-macro defines-entry)))
        (raise "Deffixequiv-mutual is intended to work on mutual recursions ~
                created using DEFINES with a flag function.  You should give ~
                the name of the defines form, not the name of the function."))
       (args (cdr (assoc :args kwd-alist)))
       (omit (cdr (assoc :omit kwd-alist)))
       (gutslist (std::defines-guts->gutslist defines-entry))
       (univ-args (get-nonfn-args args gutslist))
       (fn-args (get-fn-args args gutslist))
       (univ-omit (get-atoms omit))
       (fn-omit (get-conses omit))
       ((when (and args omit))
        (raise "Why would you provide both :args and :omit?"))
       (fns/fixequivs (if args
                          (mutual-fixequivs-from-explicit-args fn-args univ-args gutslist state)
                        (mutual-fixequivs-from-defines fn-omit univ-omit gutslist state))))
    (cons (mutual-fixequivs->fix-thm fns/fixequivs defines-entry kwd-alist world)
          (mutual-fixequivs->const/cong-thms fns/fixequivs))))

(defmacro deffixequiv-mutual (name &rest keys)
  (b* ((verbosep (let ((lst (member :verbosep keys)))
                   (and lst (cadr lst)))))
    `(with-output ,@(and (not verbosep) '(:off :all)) :stack :push
       (make-event
        (cons 'progn
              (deffixequiv-mutual-fn ',name ',keys state))))))
