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

(in-package "VL2014")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "tools/rulesets" :dir :system)
(set-state-ok t)
;; (program)

;; (defxdoc deftranssum
;;   :parents (utilities)
;;   :short "(Beta) Introduce a transparent, tagged sum of defprods.")

;; (defconst *deftranssum-valid-keywords*
;;   '(:mode
;;     :parents
;;     :short
;;     :long
;;     ))

;; #|| ;; For testing
;; (encapsulate
;;   ()
;;   (logic)
;;   (defprod foo :tag :foo ((f1 natp) (f2 natp) (f3 natp)))
;;   (defprod bar :tag :bar ((f1 natp) (f2 natp) (f3 natp)))
;;   (defprod baz :tag :baz ((f2 natp)))
;;   (deftagsum fa (:fa1 (pu natp)) (:fa2 (pa natp))))
;; ||#


;; ;; BOZO why was this stuff here?

;; ;; #!FTY
;; ;; (define get-flextypes (world)
;; ;;   "Get the database of defined flextypes."
;; ;;   (table-alist 'fty::flextypes-table world))

;; ;; #!FTY
;; ;; (def-primitive-aggregate suminfo
;; ;;   (type   ;; the superior flextypes object
;; ;;    sum    ;; the single flexsum within type
;; ;;    tags   ;; possible tags for products within type
;; ;;    ))

;; ;; #!FTY
;; ;; (define get-flexsum-from-types (name types)
;; ;;   (if (atom types)
;; ;;       nil
;; ;;     (or (and (eq (tag (car types)) :sum)
;; ;;              (eq (flexsum->name (car types)) name)
;; ;;              (car types))
;; ;;         (get-flexsum-from-types name (cdr types)))))



;; ;; #!FTY
;; ;; (define get-flexsum-info (name world)
;; ;;   :returns (suminfo?)
;; ;;   (b* ((table (get-flextypes world))
;; ;;        (entry (cdr (assoc name table)))
;; ;;        ((unless entry)
;; ;;         (raise "~x0 not found in the flextypes table." name))
;; ;;        ((unless (fty::flextypes-p entry))
;; ;;         (raise "flextypes table entry for ~x0 is malformed???" name))
;; ;;        ((fty::flextypes entry) entry)
;; ;;        ;; ((unless (equal (len entry.types) 1))
;; ;;        ;;  (raise "~x0 doesn't look like a defprod; expected one sum type but found ~x1."
;; ;;        ;;         name (len entry.types)))
;; ;;        (sum (get-flexsum-from-types name entry.types))
;; ;;        ((unless (flexsum-p sum))
;; ;;         (raise "~x0 doesn't look like a deftagsum: expected a top-level sum but found ~x1."
;; ;;                name sum))
;; ;;        ((flexsum sum) sum)
;; ;;        ;; ((unless (equal (len sum.prods) 1))
;; ;;        ;;  (raise "~x0 doesn't look like a defprod: expected a single product but found ~x1."
;; ;;        ;;         name sum.prods))
;; ;;        ;; (prod (car sum.prods))
;; ;;        ;; ((unless (flexprod-p prod))
;; ;;        ;;  (raise "~x0 doesn't look like a defprod: expected a flexprod-p but found ~x1."
;; ;;        ;;         name prod))
;; ;;        )
;; ;;     (make-suminfo :type entry
;; ;;                   :sum sum
;; ;;                   :tags (flexprods->kinds sum.prods))))

;; ;; #!FTY
;; ;; (define get-flexsum-infos (sumnames world)
;; ;;   (if (atom sumnames)
;; ;;       nil
;; ;;     (cons (get-flexsum-info (car sumnames) world)
;; ;;           (get-flexsum-infos (cdr sumnames) world))))


;; #||
;; (make-event
;;  (b* ((infos (fty::get-flexsum-infos '(foo bar fa baz) (w state))))
;;    `(defconst *suminfos* ',infos)))
;; ||#

;; #!FTY
;; (define suminfo->foop (x)
;;   (b* ((sum (suminfo->sum x))
;;        (pred (flexsum->pred sum)))
;;     pred))


;; #!FTY
;; (define suminfo->foo-fix (x)
;;   (b* ((sum (suminfo->sum x))
;;        (fix (flexsum->fix sum)))
;;     fix))


;; #||
;; (list (fty::suminfo->foop (first *suminfos*))
;;       (fty::suminfo->foop (second *suminfos*))
;;       (fty::suminfo->foop (third *suminfos*)))

;; (list (fty::suminfo->tag (first *suminfos*))
;;       (fty::suminfo->tag (second *suminfos*))
;;       (fty::suminfo->tag (third *suminfos*)))

;; (list (fty::suminfo->foo-fix (first *suminfos*))
;;       (fty::suminfo->foo-fix (second *suminfos*))
;;       (fty::suminfo->foo-fix (third *suminfos*)))

;; ||#


;; ; ------------------ Name Generation ---------------------------------------------

;; (defun dts-x (basename)
;;   (intern-in-package-of-symbol "X" basename))

;; (defun dts-recognizer-name (basename)
;;   (intern-in-package-of-symbol (concatenate 'string (symbol-name basename) "-P")
;;                                basename))

;; (defun dts-fix-name (basename)
;;   (intern-in-package-of-symbol (concatenate 'string (symbol-name basename) "-FIX")
;;                                basename))

;; (defun dts-equiv-name (basename)
;;   (intern-in-package-of-symbol (concatenate 'string (symbol-name basename) "-EQUIV")
;;                                basename))




;; ; ------------------ Sum Recognizer ----------------------------------------------


;; (defun dts-recognizer-logic-def-aux (suminfos xvar)
;;   (b* (((when (atom suminfos))
;;         nil))
;;     (cons `(,(fty::suminfo->foop (car suminfos)) ,xvar)
;;           (dts-recognizer-logic-def-aux (cdr suminfos) xvar))))

;; (defun dts-recognizer-logic-def (name suminfos)
;;   (cons 'or
;;         (dts-recognizer-logic-def-aux suminfos (dts-x name))))

;; #||
;; (dts-recognizer-logic-def 'mysum *suminfos*)
;; ||#

;; (defun dts-recognizer-exec-def-aux (suminfos xvar)
;;   (b* (((when (atom suminfos))
;;         nil)
;;        ((when (atom (cdr suminfos)))
;;         ;; last one, just use "otherwise"
;;         `((otherwise
;;            (,(fty::suminfo->foop (car suminfos)) ,xvar))))
;;        (tags (fty::suminfo->tags (car suminfos))))
;;     (cons `(,(if (consp (cdr tags)) tags (car tags))
;;             (,(fty::suminfo->foop (car suminfos)) ,xvar))
;;           (dts-recognizer-exec-def-aux (cdr suminfos) xvar))))

;; (defun dts-recognizer-exec-def (name suminfos)
;;   (let ((xvar (dts-x name)))
;;     `(case (tag ,xvar)
;;        . ,(dts-recognizer-exec-def-aux suminfos xvar))))

;; #||
;; (dts-recognizer-exec-def 'mysum *suminfos*)
;; ||#

;; (defun dts-recognizer-def (name suminfos)
;;   (let ((xvar (dts-x name)))
;;     `(define ,(dts-recognizer-name name) (,xvar)
;;        :parents (,name)
;;        :short ,(cat "Recognizer for @(see " (xdoc::full-escape-symbol name) ") structures.")
;;        :returns bool
;;        (mbe :logic ,(dts-recognizer-logic-def name suminfos)
;;             :exec ,(dts-recognizer-exec-def name suminfos)))))

;; #||
;; (dts-recognizer-def 'mysum *suminfos*)
;; ||#


;; ; ------------------ Basic Theorems ----------------------------------------------

;; (defun dts-member-implies-sum-thm (name suminfo)

;;   ;; This sumuces theorems like this:
;;   ;; (defthm vl-atomguts-p-when-vl-constint-p
;;   ;;   (implies (vl-constint-p x)
;;   ;;            (vl-atomguts-p x)))

;;   (b* ((xvar     (dts-x name))
;;        (sum-name (dts-recognizer-name name))
;;        (mem-name (fty::suminfo->foop suminfo))
;;        (thm-name (intern-in-package-of-symbol
;;                   (concatenate 'string (symbol-name sum-name) "-WHEN-"
;;                                (symbol-name mem-name))
;;                   name)))
;;     `(defthm ,thm-name
;;        (implies (,mem-name ,xvar)
;;                 (,sum-name ,xvar))
;;        ;; Without this we got KILLED by vl-modelement-p reasoning in the proofs
;;        ;; of sizing, etc.
;;        :rule-classes ((:rewrite :backchain-limit-lst 1)))))

;; (defun dts-member-implies-sum-thms (name suminfos)
;;   (if (atom suminfos)
;;       nil
;;     (cons (dts-member-implies-sum-thm name (car suminfos))
;;           (dts-member-implies-sum-thms name (cdr suminfos)))))

;; #||
;; (dts-member-implies-sum-thms 'mysum *suminfos*)
;; ||#

;; (defun dts-tag-equalities (xvar tags)
;;   (if (atom tags)
;;       nil
;;     (cons `(equal (tag ,xvar) ,(car tags))
;;           (dts-tag-equalities xvar (cdr tags)))))

;; (defun dts-by-tag-thm (name suminfo)

;;   ;; This sumuces theorems like this:
;;   ;; (defthm vl-constint-p-by-tag-when-vl-atomguts-p
;;   ;;   (implies (and (equal (tag x) :vl-constint)
;;   ;;                 (vl-atomguts-p x))
;;   ;;            (vl-constint-p x)))

;;   (b* ((xvar     (dts-x name))
;;        (sum-name (dts-recognizer-name name))
;;        (mem-name (fty::suminfo->foop suminfo))
;;        (mem-tags  (fty::suminfo->tags suminfo))
;;        (thm-name (intern-in-package-of-symbol
;;                   (concatenate 'string (symbol-name mem-name)
;;                                "-BY-TAG-WHEN-"
;;                                (symbol-name sum-name))
;;                   name)))
;;     `(defthm ,thm-name
;;        (implies (and (or . ,(dts-tag-equalities xvar mem-tags))
;;                      (,sum-name ,xvar))
;;                 (,mem-name ,xvar)))))

;; (defun dts-by-tag-thms (name suminfos)
;;   (if (atom suminfos)
;;       nil
;;     (cons (dts-by-tag-thm name (car suminfos))
;;           (dts-by-tag-thms name (cdr suminfos)))))

;; #||
;; (dts-by-tag-thms 'mysum *suminfos*)
;; ||#


;; (defun dts-when-invalid-tag-hyps (name suminfos)
;;   (b* (((when (atom suminfos))
;;         nil)
;;        (xvar (dts-x name))
;;        (tags  (fty::suminfo->tags (car suminfos))))
;;     (cons `(not (or . ,(dts-tag-equalities xvar tags)))
;;           (dts-when-invalid-tag-hyps name (cdr suminfos)))))

;; (defun dts-when-invalid-tag-thm (name suminfos)
;;   ;; Generates a theorem like:
;;   ;; (defthm vl-atomicstmt-p-when-invalid-tag
;;   ;;   (implies (and (not (equal (tag x) :vl-nullstmt))
;;   ;;                 (not (equal (tag x) :vl-assignstmt))
;;   ;;                 (not (equal (tag x) :vl-deassignstmt))
;;   ;;                 (not (equal (tag x) :vl-enablestmt))
;;   ;;                 (not (equal (tag x) :vl-disablestmt))
;;   ;;                 (not (equal (tag x) :vl-eventtriggerstmt)))
;;   ;;          (not (vl-atomicstmt-p x)))
;;   ;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))
;;   (b* ((xvar     (dts-x name))
;;        (sum-name (dts-recognizer-name name))
;;        (thm-name (intern-in-package-of-symbol
;;                   (concatenate 'string (symbol-name sum-name)
;;                                "-WHEN-INVALID-TAG")
;;                   name)))
;;     `(defthm ,thm-name
;;        (implies (and . ,(dts-when-invalid-tag-hyps name suminfos))
;;                 (not (,sum-name ,xvar)))
;;        :rule-classes ((:rewrite :backchain-limit-lst 0)))))

;; (defun dts-fwd-disjuncts (name suminfos)
;;   (b* (((when (atom suminfos))
;;         nil)
;;        (xvar (dts-x name))
;;        (tags (fty::suminfo->tags (car suminfos))))
;;     (append (dts-tag-equalities xvar tags)
;;             (dts-fwd-disjuncts name (cdr suminfos)))))

;; (defun dts-fwd-thm (name suminfos)
;;   ;; Generates a theorem like:
;;   ;; (defthm tag-when-vl-genelement-p-forward
;;   ;;   (implies (vl-genelement-p x)
;;   ;;            (or (equal (tag x) :vl-genbase)
;;   ;;                (equal (tag x) :vl-genif)
;;   ;;                (equal (tag x) :vl-gencase)
;;   ;;                (equal (tag x) :vl-genloop)
;;   ;;                (equal (tag x) :vl-genblock)
;;   ;;                (equal (tag x) :vl-genarray)))
;;   ;;   :rule-classes :forward-chaining)
;;   (b* ((xvar     (dts-x name))
;;        (sum-name (dts-recognizer-name name))
;;        (thm-name (intern-in-package-of-symbol
;;                   (concatenate 'string
;;                                "TAG-WHEN-" (symbol-name sum-name) "-FORWARD")
;;                   name)))
;;     `(defthm ,thm-name
;;        (implies (,sum-name ,xvar)
;;                 (or . ,(dts-fwd-disjuncts name suminfos)))
;;        :hints(("Goal" :by ,(intern-in-package-of-symbol
;;                             (concatenate 'string (symbol-name sum-name)
;;                                          "-WHEN-INVALID-TAG")
;;                             name)))
;;        :rule-classes ((:forward-chaining)))))

;; #||
;; (dts-fwd-thm 'mysum *suminfos*)
;; ||#




;; ; ----------------------- Fixing Function --------------------------------------

;; (defun dts-fix-def (name suminfos)
;;   (b* (((when (atom suminfos))
;;         (er hard? 'deftranssum "Can't define transparent sum ~x0 with no member types." name))
;;        (info1   (car suminfos))
;;        (mem-fix (fty::suminfo->foo-fix info1))
;;        (sum-fix (dts-fix-name name))
;;        (sum-p   (dts-recognizer-name name))
;;        (xvar    (dts-x name)))
;;     `(define ,sum-fix ((,xvar ,sum-p))
;;        :parents (,name)
;;        :short ,(cat "Fixing function for @(see " (xdoc::full-escape-symbol name) ") structures.")
;;        :returns name
;;        :inline t
;;        (mbe :logic (if (,sum-p ,xvar)
;;                        ,xvar
;;                      (,mem-fix ,xvar))
;;             :exec ,xvar))))

;; (defun dts-fix-thms (name)
;;   (b* ((sum-fix (dts-fix-name name))
;;        (sum-p   (dts-recognizer-name name))
;;        (xvar    (dts-x name)))
;;     `(defsection dts-fix-thms
;;        :extension ,sum-fix
;;        (defthm ,(intern-in-package-of-symbol
;;                 (concatenate 'string (symbol-name sum-fix) "-WHEN-" (symbol-name sum-p))
;;                 name)
;;         (implies (,sum-p ,xvar)
;;                  (equal (,sum-fix ,xvar)
;;                         ,xvar))
;;         :hints(("Goal" :in-theory (disable ,sum-p))))

;;       (defthm ,(intern-in-package-of-symbol
;;                 (concatenate 'string (symbol-name sum-p) "-OF-" (symbol-name sum-fix))
;;                 name)
;;         (,sum-p (,sum-fix ,xvar))
;;         :hints(("Goal" :in-theory (disable ,sum-p)))))))

;; #||
;; (dts-fix-def 'mysum *suminfos*)
;; (dts-fix-thms 'mysum)
;; ||#


;; (defun deftranssum-fn (name other-args kwd-alist other-events state)
;;   (b* ((__function__ 'deftranssum)
;;        (?mksym-package-symbol name)

;;        (short (std::getarg :short nil kwd-alist))
;;        (long  (std::getarg :long nil kwd-alist))
;;        (mode  (std::getarg :mode (default-defun-mode (w state)) kwd-alist))

;;        (parents-p (assoc :parents kwd-alist))
;;        (parents   (cdr parents-p))
;;        (parents   (if parents-p
;;                       parents
;;                     (or (xdoc::get-default-parents (w state))
;;                         '(acl2::undocumented))))

;;        ((unless (or (eq mode :logic)
;;                     (eq mode :program)))
;;         (raise ":mode must be one of :logic or :program, but is ~x0." mode))
;;        ((unless (or (not short)
;;                     (stringp short)))
;;         (raise ":short must be a string or nil, but is ~x0." short))
;;        ((unless (or (not long)
;;                     (stringp long)))
;;         (raise ":long must be a string or nil, but is ~x0." long))

;;        (long (or long
;;                  (and parents
;;                       "<p>This is an ordinary @(see vl2014::deftranssum) of aggregates.</p>")))

;;        ((unless (std::tuplep 1 other-args))
;;         (raise "deftranssum should be given exactly one non-keyword argument, but got ~x0"
;;                other-args))

;;        (foo-p     (dts-recognizer-name name))
;;        (foo-fix   (dts-fix-name name))
;;        (foo-equiv (dts-equiv-name name))
;;        (x         (dts-x name))

;;        (sumnames (first other-args))
;;        (suminfos (fty::get-flexsum-infos sumnames (w state)))
;;        (def       (dts-recognizer-def name suminfos))
;;        (fix-def   (dts-fix-def name suminfos))

;;        ((when (eq mode :program))
;;         `(defsection ,name
;;            ,@(and parents `(:parents ,parents))
;;            ,@(and short   `(:short ,short))
;;            ,@(and long    `(:long ,long))
;;            (program)
;;            ,def
;;            ,fix-def
;;            . ,other-events))

;;        (events
;;         `((logic)
;;           (local (in-theory (enable tag-reasoning)))
;;           ,def
;;           (local (in-theory (enable ,foo-p)))

;;           ,fix-def
;;           (local (in-theory (enable ,foo-fix)))

;;           (defsection-progn dts-rec-thms
;;             :extension ,foo-p

;;             (defthm ,(mksym 'consp-when- foo-p)
;;               (implies (,foo-p ,x)
;;                        (consp ,x))
;;               :rule-classes :compound-recognizer)

;;             ,@(dts-member-implies-sum-thms name suminfos)
;;             ,@(dts-by-tag-thms name suminfos)
;;             ,(dts-when-invalid-tag-thm name suminfos)
;;             ,(dts-fwd-thm name suminfos))

;;           ,(dts-fix-thms name)

;;           (defsection-progn ,foo-equiv
;;             :parents (,name)
;;             :short ,(cat "Basic equivalence relation for @(see " (xdoc::full-escape-symbol foo-p) ") structures.")

;;             (fty::deffixtype ,name
;;               :pred  ,foo-p
;;               :equiv ,foo-equiv
;;               :fix   ,foo-fix
;;               :define t
;;               :forward t))

;;           ;; BOZO maybe generate fast functions?
;;           ;; BOZO some kind of pattern-match macros?
;;           )))

;;     `(encapsulate
;;        ()
;;        (defxdoc ,name
;;          ,@(and parents `(:parents ,parents))
;;          ,@(and short   `(:short ,short))
;;          ,@(and long    `(:long ,long)))
;;        (encapsulate () . ,events)
;;        . ,other-events)))

;; (defmacro deftranssum (name &rest args)
;;   (b* ((__function__ 'deftranssum)
;;        ((unless (symbolp name))
;;         (raise "Name must be a symbol."))
;;        (ctx (list 'deftranssum name))
;;        ((mv main-stuff other-events) (std::split-/// ctx args))
;;        ((mv kwd-alist other-args)
;;         (std::extract-keywords ctx *deftranssum-valid-keywords* main-stuff nil)))
;;     ;; BOZO Add with-output stuff eventually
;;     `(make-event
;;       `(progn ,(deftranssum-fn ',name ',other-args ',kwd-alist ',other-events state)
;;               (value-triple '(deftranssum ,',name))))))

;; #||
;; (local (defthm fa-p-possible-tags
;;          (implies (fa-p x)
;;                   (or (equal (tag x) :fa1)
;;                       (equal (tag x) :fa2)))
;;          :hints(("Goal" :in-theory (enable fa-p tag)))
;;          :rule-classes :forward-chaining))

;; (deftranssum mysum
;;   :mode :logic
;;   (foo bar fa baz))
;; ||#

