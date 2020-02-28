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
(include-book "../../parsetree")
(include-book "../../mlib/scopestack")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))


; Lining Up Parameter Declarations with Override Values -----------------------
;
; Instances can have override parameters using either named or unnamed format.
; We now pair up the parameter declarations with their replacements.  We
; produce the list in parameter-declaration order, so that later we can
; properly account for dependencies between the parameters.

(local (xdoc::set-default-parents vl-make-paramdecloverrides))

(defprojection vl-namedparamvaluelist->names ((x vl-namedparamvaluelist-p))
  :returns (names string-listp)
  (vl-namedparamvalue->name x))

(define vl-find-namedparamvalue ((name stringp)
                                 (args vl-namedparamvaluelist-p))
  :returns (arg (equal (vl-namedparamvalue-p arg) (if arg t nil)))
  (b* (((when (atom args))
        nil)
       (arg1 (vl-namedparamvalue-fix (car args)))
       ((when (equal (vl-namedparamvalue->name arg1)
                     (string-fix name)))
        arg1))
    (vl-find-namedparamvalue name (cdr args)))
  ///
  (defthm vl-find-namedparamvalue-when-member-of-vl-namedparamvaluelist->names
    (implies (and (member name (vl-namedparamvaluelist->names args))
                  (stringp name))
             (vl-find-namedparamvalue name args))))

(define vl-nonlocal-paramdecls
  :short "Filter parameter declarations, keeping only the non-local declarations."
  ((x vl-paramdecllist-p))
  :returns (nonlocal-params vl-paramdecllist-p)
  (cond ((atom x)
         nil)
        ((vl-paramdecl->localp (car x))
         (vl-nonlocal-paramdecls (cdr x)))
        (t
         (cons (vl-paramdecl-fix (car x))
               (vl-nonlocal-paramdecls (cdr x)))))
  ///
  (defthm vl-nonlocal-paramdecls-of-atom
    (implies (atom x)
             (equal (vl-nonlocal-paramdecls x)
                    nil)))
  (defthm vl-nonlocal-paramdecls-of-cons
    (equal (vl-nonlocal-paramdecls (cons a x))
           (if (vl-paramdecl->localp a)
               (vl-nonlocal-paramdecls x)
             (cons (vl-paramdecl-fix a) (vl-nonlocal-paramdecls x))))))

(defprod vl-paramdecloverride
  :short "Paired up parameter declaration with its override values from a
          module instance."
  ((decl     vl-paramdecl-p)
   (override vl-maybe-paramvalue-p)))

(fty::deflist vl-paramdecloverridelist
  :elt-type vl-paramdecloverride-p
  :elementp-of-nil nil
  :true-listp nil)

(define vl-make-paramdecloverrides-named
  :parents (unparameterization)
  :short "Line up named parameter arguments with parameter declarations."
  ((formals vl-paramdecllist-p       "In proper order, from the submodule.")
   (actuals vl-namedparamvaluelist-p "From the instance."))
  :returns (overrides vl-paramdecloverridelist-p)
  (b* (((when (atom formals))
        nil)
       ((vl-paramdecl decl1) (vl-paramdecl-fix (car formals)))

       ((when decl1.localp)
        ;; Local parameters don't get any explicit overrides.
        (cons (make-vl-paramdecloverride :decl decl1
                                         :override nil)
              (vl-make-paramdecloverrides-named (cdr formals) actuals)))

       (look  (vl-find-namedparamvalue decl1.name actuals))
       (value (and look
                   (vl-namedparamvalue->value look))))

    (cons (make-vl-paramdecloverride :decl decl1
                                     :override value)
          (vl-make-paramdecloverrides-named (cdr formals) actuals))))

(define vl-make-paramdecloverrides-indexed
  :short "Line up positional parameter arguments with parameter declarations."
  ((formals vl-paramdecllist-p  "In proper order, from the submodule.")
   (actuals vl-paramvaluelist-p "In proper order, from the instance."))
  :guard (<= (len actuals) (len (vl-nonlocal-paramdecls formals)))
  :returns (overrides vl-paramdecloverridelist-p)
  (b* (((when (atom formals))
        nil)
       ((vl-paramdecl decl1) (vl-paramdecl-fix (car formals)))

       ((when decl1.localp)
        ;; Local parameters don't get any explicit overrides.
        (cons (make-vl-paramdecloverride :decl decl1
                                         :override nil)
              (vl-make-paramdecloverrides-indexed (cdr formals) actuals)))

       ;; We can run out of actuals and that's okay, all remaining formals
       ;; just get no explicit values.
       (value (and (consp actuals)
                   (vl-paramvalue-fix (first actuals)))))

    (cons (make-vl-paramdecloverride :decl decl1
                                     :override value)
          (vl-make-paramdecloverrides-indexed (cdr formals)
                                              (and (consp actuals)
                                                   (rest actuals))))))

(define vl-make-paramdecloverrides
  :parents (unparameterization)
  :short "Line up parameter arguments with parameter declarations."
  ((formals  vl-paramdecllist-p "In proper order, from the submodule.")
   (actuals  vl-paramargs-p     "From the instance.")
   (bad-instance-fatalp booleanp)
   (warnings vl-warninglist-p   "Warnings accumulator for the superior module."))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription)
      (warnings  vl-warninglist-p)
      (overrides vl-paramdecloverridelist-p))
  (b* ((formals           (vl-paramdecllist-fix formals))

       ((unless (uniquep (vl-paramdecllist->names formals)))
        ;; Not a great place to check for this, but better safe than sorry.
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "parameters are not unique: ~&1."
                   :args (list nil (duplicated-members (vl-paramdecllist->names formals))))
            nil)))

    (vl-paramargs-case actuals

      (:vl-paramargs-named
       (b* ((actual-names (vl-namedparamvaluelist->names actuals.args))
            (?formal-names (vl-paramdecllist->names (vl-nonlocal-paramdecls formals)))

            ((unless (uniquep actual-names))
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "multiple occurrences of parameter arguments: ~&1."
                        :args (list nil (duplicated-members actual-names)))
                 nil))

            (illegal-names
             ;; Actuals that are NOT actually declarations.
             (difference (mergesort actual-names) (mergesort formal-names)))
            (warnings (if illegal-names
                          (warn :type :vl-bad-instance
                                :msg "parameter~s1 ~&2 ~s3."
                                :args (list nil
                                            (if (vl-plural-p illegal-names) "s" "")
                                            illegal-names
                                            (if (vl-plural-p illegal-names) "do not exist" "does not exist"))
                                :fatalp bad-instance-fatalp)
                        warnings))

            ;; No confusion: everything is unique, the instance mentions only
            ;; the non-localparams, etc.  Good enough.
            (overrides (vl-make-paramdecloverrides-named formals actuals.args)))
         (mv t (ok) overrides)))

      (:vl-paramargs-plain
       (b* ((num-formals (len (vl-nonlocal-paramdecls formals)))
            (num-actuals (len actuals.args))
            ((unless (<= num-actuals num-formals))
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "too many parameter values: ~x1 (non-local) ~
                              parameter~s2, but is given ~x3 parameter argument~s4."
                        :args (list nil
                                    num-formals
                                    (if (eql num-formals 1) "" "s")
                                    num-actuals
                                    (if (eql num-actuals 1) "" "s")))
                 nil))

            ;; Else no worries, not too many parameters
            (overrides (vl-make-paramdecloverrides-indexed formals actuals.args)))
         (mv t (ok) overrides))))))
