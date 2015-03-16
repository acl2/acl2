; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "STD")
(include-book "std/util/define" :dir :system)
(include-book "std/util/defenum" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(set-state-ok t)
(program)

;; (defxdoc defoption
;;   :parents (vl2014::utilities)
;;   :short "Define an option type."
;;   :long "<p>BOZO eventually integrate this into @(see std/util).</p>

;; <p>Example:</p>
;; @({
;;     (defoption maybe-foop
;;       foop
;;       :parents (foop)
;;       :short \"Either a foop or nothing.\"
;;       :long \"Blah blah blah\")
;; })

;; <p>General form:</p>
;; @({
;;     (defoption option-name            ;; name of new option type
;;       regular-name                    ;; name of original base type

;;       ;; definition controls
;;       [:mode          mode]           ;; default: current defun-mode
;;       [:guard         guard]          ;; default: t
;;       [:verify-guards verify-guards]  ;; default: t
;;       [:guard-debug   guard-debug]    ;; default: nil
;;       [:guard-hints   guard-hints]    ;; default: nil

;;       ;; xdoc integration
;;       [:parents       parents]
;;       [:short         short]
;;       [:long          long]

;;       ;; fixtype integration
;;       [:fix           fix-name]       ;; default: option-name-fix
;;       [:equiv         equiv-name]     ;; default: option-name-equiv

;;       ;; misc options
;;       [:verbosep      verbosep]       ;; default: nil

;;       ;; associated events
;;       [/// rest-events]               ;; as in define
;;       )
;; })

;; <p>BOZO nice documentation.</p>")

;; (defconst *defoption-valid-keywords*
;;   '(:mode
;;     :guard
;;     :verify-guards
;;     :guard-debug
;;     :guard-hints
;;     :parents
;;     :short
;;     :long
;;     :fix
;;     :equiv
;;     :verbosep
;;     :pkg))

;; (defun defoption-fn (name base-type kwd-alist rest-events state)
;;   (declare (xargs :mode :program))
;;   (b* ((__function__ 'defoption)

;;        ((unless (and (symbolp name)
;;                      (not (booleanp name))
;;                      (not (keywordp name))))
;;         (raise "Invalid name for new option type: ~x0." name))

;;        ((unless (and (symbolp base-type)
;;                      (not (booleanp base-type))
;;                      (not (keywordp base-type))))
;;         (raise "Invalid base type for new option type: ~x0." base-type))

;;        (name-without-p (std::strip-p-from-symbol name))

;;        ;; Special variables that are reserved by deflist.
;;        (x (intern-in-package-of-symbol "X" name))
;;        (mode             (getarg :mode
;;                                  (default-defun-mode (w state))
;;                                  kwd-alist))
;;        (verify-guards    (getarg :verify-guards
;;                                  ;; Verify guards unless in program mode
;;                                  (eq mode :logic)
;;                                  kwd-alist))
;;        (guard            (getarg :guard            t        kwd-alist))
;;        (guard-debug      (getarg :guard-debug      nil      kwd-alist))
;;        (guard-hints      (getarg :guard-hints      nil      kwd-alist))
;;        (short            (getarg :short            nil      kwd-alist))
;;        (long             (getarg :long             nil      kwd-alist))

;;        (mksym-package-symbol (getarg :pkg name kwd-alist))

;;        (fix              (getarg :fix (mksym name-without-p '-fix) kwd-alist))
;;        (equiv            (getarg :equiv (mksym name-without-p '-equiv) kwd-alist))

;;        (parents-p (assoc :parents kwd-alist))
;;        (parents   (cdr parents-p))
;;        (parents   (if parents-p
;;                       parents
;;                     (or (xdoc::get-default-parents (w state))
;;                         '(acl2::undocumented))))

;;        ((unless (booleanp verify-guards))
;;         (raise ":verify-guards must be a boolean, but is ~x0." verify-guards))
;;        ((unless (or (eq mode :logic)
;;                     (eq mode :program)))
;;         (raise ":mode must be one of :logic or :program, but is ~x0." mode))

;;        (short (or short
;;                   (and parents
;;                        (concatenate
;;                         'string "@(call " (symbol-name name)
;;                                  ") is an option type that recognizes @('nil') or "
;;                                  "any valid @(see " (symbol-name base-type) ")."))))
;;        (long (or long
;;                  (and parents
;;                       "<p>This is an ordinary @(see std::defoption).</p>")))

;;        (looks-already-defined-p
;;         (or (not (eq (getprop name 'acl2::formals :none 'acl2::current-acl2-world
;;                               (w state))
;;                      :none))
;;             (not (eq (getprop name 'acl2::macro-args :none 'acl2::current-acl2-world
;;                               (w state))
;;                      :none))))

;;        (name-def
;;         (if looks-already-defined-p
;;             `(value-triple
;;               (cw "~|;; not introducing ~s0 since it's already defined.~%"
;;                   ',name))
;;           `(defund ,name (,x)
;;              (declare (xargs :guard ,guard
;;                              :guard-debug ,guard-debug
;;                              :guard-hints ,guard-hints
;;                              :verify-guards ,verify-guards
;;                              :mode ,mode))
;;                     (or (not ,x)
;;                         (,base-type ,x)))))

;;        (fixtypes-alist (fty::get-fixtypes-alist (w state)))
;;        (base-type-info (fty::find-fixtype base-type fixtypes-alist))
;;        ((unless (fty::fixtype-p base-type-info))
;;         (raise "Fixtype information for base type ~x0 not found." base-type))
;;        (base-type-fix   (fty::fixtype->fix base-type-info))
;;        (base-type-equiv (fty::fixtype->equiv base-type-info))

;;        (fix-def `(defund-inline ,fix (,x)
;;                    (declare (xargs :guard (,name ,x)))
;;                    (mbe :logic (if ,x
;;                                    (,base-type-fix ,x)
;;                                  nil)
;;                         :exec ,x)))

;;        ((when (eq mode :program))
;;         `(defsection ,name
;;            ,@(and parents `(:parents ,parents))
;;            ,@(and short   `(:short ,short))
;;            ,@(and long    `(:long ,long))
;;            (program)
;;            ,name-def
;;            ,fix-def
;;            ,@rest-events))

;;        (events
;;         `((logic)
;;           (set-inhibit-warnings ;; implicitly local
;;            "theory" "non-rec")
;;           (value-triple (cw "~|Defoption: checking base type ~x0.~%" ',base-type))

;;           (local (defthm defoption-lemma-booleanp
;;                    (booleanp (,base-type ,x))
;;                    :rule-classes :type-prescription
;;                    :hints((and stable-under-simplificationp
;;                                '(:in-theory (enable ,base-type))))))

;;           (local (defthm defoption-lemma-non-nil
;;                    (not (,base-type nil))
;;                    :rule-classes nil
;;                    :hints((and stable-under-simplificationp
;;                                '(:in-theory (enable ,base-type))))))

;;           (local (defthm defoption-lemma-fix-non-nil
;;                    (,base-type-fix x)
;;                    :hints(("goal" :use ((:theorem (,base-type (,base-type-fix x)))
;;                                        defoption-lemma-non-nil)
;;                            :in-theory '((,base-type)))
;;                           (and stable-under-simplificationp
;;                                '(:in-theory (enable))))))

;;           (value-triple (cw "~|Defoption: introducing option recognizer ~x0.~%"
;;                             ',name))
;;           ,name-def

;;           (local (in-theory (enable ,name)))

;;           (defthm ,(mksym name '-when- base-type)
;;             (implies (,base-type ,x)
;;                      (,name ,x)))

;;           (defthm ,(mksym base-type '-when- name)
;;             (implies (and (,name ,x)
;;                           (double-rewrite ,x))
;;                      (,base-type ,x)))

;;           (value-triple (cw "~|Defoption: introducing fixing function ~x0.~%"
;;                             ',fix))

;;           ,fix-def

;;           (local (in-theory (e/d (,fix) (,name))))

;;           (defthm ,(mksym name '-of- fix)
;;             (,name (,fix ,x)))

;;           (defthm ,(mksym fix '-when- name)
;;             (implies (,name ,x)
;;                      (equal (,fix ,x) ,x)))

;;           (defthm ,(mksym fix '-under-iff)
;;             (iff (,fix ,x) ,x))

;;           ;; (defthm ,(mksym fix '-under- base-type-equiv)
;;           ;;   (implies ,x
;;           ;;            (,base-type-equiv (,fix ,x)
;;           ;;                              ,x)))

;;           (fty::deffixtype ,name
;;             :pred ,name
;;             :fix ,fix
;;             :equiv ,equiv
;;             :define t
;;             :forward t)

;;           (defrefinement ,equiv ,base-type-equiv
;;             :hints((and stable-under-simplificationp
;;                         '(:in-theory (enable ,base-type-equiv))))))))

;;     `(defsection ,name
;;        ,@(and parents `(:parents ,parents))
;;        ,@(and short   `(:short ,short))
;;        ,@(and long    `(:long ,long))
;;        ;; keep all our theory stuff bottled up.  BOZO encapsulate is slow,
;;        ;; better to use a progn here.
;;        (encapsulate ()
;;          . ,events)
;;        ;; now do the rest of the events with name enabled, so they get included
;;        ;; in the section
;;        . ,(and rest-events
;;                `((value-triple (cw "~|Defoption: submitting /// events.~%"))
;;                  (with-output
;;                    :stack :pop
;;                    (progn
;;                      (local (in-theory (enable ,name)))
;;                      . ,rest-events)))))))


;; (defmacro defoption (name &rest args)
;;   (b* ((__function__ 'defoption)
;;        ((unless (symbolp name))
;;         (raise "Name must be a symbol."))
;;        (ctx (list 'defoption name))
;;        ((mv main-stuff rest-events) (split-/// ctx args))
;;        ((mv kwd-alist base-type)
;;         (extract-keywords ctx *defoption-valid-keywords* main-stuff nil))
;;        ((unless (tuplep 1 base-type))
;;         (raise "Wrong number of arguments to defoption."))
;;        (base-type (first base-type))
;;        (verbosep (getarg :verbosep nil kwd-alist)))
;;     `(with-output
;;        :stack :push
;;        ,@(if verbosep
;;              nil
;;            '(:gag-mode t :off (acl2::summary
;;                                acl2::observation
;;                                acl2::prove
;;                                acl2::proof-tree
;;                                acl2::event)))
;;        (make-event
;;         `(progn ,(defoption-fn ',name ',base-type ',kwd-alist ',rest-events state)
;;                 (value-triple '(defoption ,',name)))))))


;; ;; BOZO add nice test suite
(defmacro defoption (&rest args)
  `(fty::defoption . ,args))
