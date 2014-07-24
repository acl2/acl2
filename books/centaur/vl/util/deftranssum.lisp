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
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "std/strings/cat" :dir :system)
(set-state-ok t)
(program)

(defxdoc deftranssum
  :parents (utilities)
  :short "(Beta) Introduce a transparent, tagged sum of defprods.")

(defconst *deftranssum-valid-keywords*
  '(:mode
    :parents
    :short
    :long
    ))

#|| ;; For testing
(encapsulate
  ()
  (logic)
  (defprod foo :tag :foo ((f1 natp) (f2 natp) (f3 natp)))
  (defprod bar :tag :bar ((f1 natp) (f2 natp) (f3 natp)))
  (defprod baz :tag :baz ((f2 natp))))
||#

#!FTY
(define get-flextypes (world)
  "Get the database of defined flextypes."
  (table-alist 'fty::flextypes-table world))

#!FTY
(def-primitive-aggregate prodinfo
  (type   ;; the superior flextypes object
   sum    ;; the single flexsum within type
   prod   ;; the single flexprod within sum
   ))

#!FTY
(define get-flexprod-info (name world)
  :returns (prodinfo?)
  (b* ((table (get-flextypes world))
       (entry (cdr (assoc name table)))
       ((unless entry)
        (raise "~x0 not found in the flextypes table." name))
       ((unless (fty::flextypes-p entry))
        (raise "flextypes table entry for ~x0 is malformed???" name))
       ((fty::flextypes entry) entry)
       ((unless (equal (len entry.types) 1))
        (raise "~x0 doesn't look like a defprod; expected one sum type but found ~x1."
               name (len entry.types)))
       (sum (car entry.types))
       ((unless (flexsum-p sum))
        (raise "~x0 doesn't look like a defprod: expected a top-level sum but found ~x1."
               name sum))
       ((flexsum sum) sum)
       ((unless (equal (len sum.prods) 1))
        (raise "~x0 doesn't look like a defprod: expected a single product but found ~x1."
               name sum.prods))
       (prod (car sum.prods))
       ((unless (flexprod-p prod))
        (raise "~x0 doesn't look like a defprod: expected a flexprod-p but found ~x1."
               name prod)))
    (make-prodinfo :type entry
                   :sum sum
                   :prod prod)))

#!FTY
(define get-flexprod-infos (prodnames world)
  (if (atom prodnames)
      nil
    (cons (get-flexprod-info (car prodnames) world)
          (get-flexprod-infos (cdr prodnames) world))))


#||
(make-event
 (b* ((infos (fty::get-flexprod-infos '(foo bar baz) (w state))))
   `(defconst *prodinfos* ',infos)))
||#

#!FTY
(define prodinfo->foop (x)
  (b* ((sum (prodinfo->sum x))
       (pred (flexsum->pred sum)))
    pred))

#!FTY
(define prodinfo->tag (x)
  (b* ((prod (prodinfo->prod x))
       (kind (flexprod->kind prod)))
    kind))

#!FTY
(define prodinfo->foo-fix (x)
  (b* ((sum (prodinfo->sum x))
       (fix (flexsum->fix sum)))
    fix))


#||
(list (fty::prodinfo->foop (first *prodinfos*))
      (fty::prodinfo->foop (second *prodinfos*))
      (fty::prodinfo->foop (third *prodinfos*)))

(list (fty::prodinfo->tag (first *prodinfos*))
      (fty::prodinfo->tag (second *prodinfos*))
      (fty::prodinfo->tag (third *prodinfos*)))

(list (fty::prodinfo->foo-fix (first *prodinfos*))
      (fty::prodinfo->foo-fix (second *prodinfos*))
      (fty::prodinfo->foo-fix (third *prodinfos*)))

||#


; ------------------ Name Generation ---------------------------------------------

(defun dts-x (basename)
  (intern-in-package-of-symbol "X" basename))

(defun dts-recognizer-name (basename)
  (intern-in-package-of-symbol (concatenate 'string (symbol-name basename) "-P")
                               basename))

(defun dts-fix-name (basename)
  (intern-in-package-of-symbol (concatenate 'string (symbol-name basename) "-FIX")
                               basename))

(defun dts-equiv-name (basename)
  (intern-in-package-of-symbol (concatenate 'string (symbol-name basename) "-EQUIV")
                               basename))




; ------------------ Sum Recognizer ----------------------------------------------


(defun dts-recognizer-logic-def-aux (prodinfos xvar)
  (b* (((when (atom prodinfos))
        nil))
    (cons `(,(fty::prodinfo->foop (car prodinfos)) ,xvar)
          (dts-recognizer-logic-def-aux (cdr prodinfos) xvar))))

(defun dts-recognizer-logic-def (name prodinfos)
  (cons 'or
        (dts-recognizer-logic-def-aux prodinfos (dts-x name))))

#||
(dts-recognizer-logic-def 'mysum *prodinfos*)
||#

(defun dts-recognizer-exec-def-aux (prodinfos xvar)
  (b* (((when (atom prodinfos))
        nil)
       ((when (atom (cdr prodinfos)))
        ;; last one, just use "otherwise"
        `((otherwise
           (,(fty::prodinfo->foop (car prodinfos)) ,xvar)))))
    (cons `(,(fty::prodinfo->tag (car prodinfos))
            (,(fty::prodinfo->foop (car prodinfos)) ,xvar))
          (dts-recognizer-exec-def-aux (cdr prodinfos) xvar))))

(defun dts-recognizer-exec-def (name prodinfos)
  (let ((xvar (dts-x name)))
    `(case (tag ,xvar)
       . ,(dts-recognizer-exec-def-aux prodinfos xvar))))

#||
(dts-recognizer-exec-def 'mysum *prodinfos*)
||#

(defun dts-recognizer-def (name prodinfos)
  (let ((xvar (dts-x name)))
    `(defund ,(dts-recognizer-name name) (,xvar)
       (declare (xargs :guard t))
       (mbe :logic ,(dts-recognizer-logic-def name prodinfos)
            :exec ,(dts-recognizer-exec-def name prodinfos)))))

#||
(dts-recognizer-def 'mysum *prodinfos*)
||#


; ------------------ Basic Theorems ----------------------------------------------

(defun dts-member-implies-sum-thm (name prodinfo)

  ;; This produces theorems like this:
  ;; (defthm vl-atomguts-p-when-vl-constint-p
  ;;   (implies (vl-constint-p x)
  ;;            (vl-atomguts-p x)))

  (b* ((xvar     (dts-x name))
       (sum-name (dts-recognizer-name name))
       (mem-name (fty::prodinfo->foop prodinfo))
       (thm-name (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name sum-name) "-WHEN-"
                               (symbol-name mem-name))
                  name)))
    `(defthm ,thm-name
       (implies (,mem-name ,xvar)
                (,sum-name ,xvar))
       ;; Without this we got KILLED by vl-modelement-p reasoning in the proofs
       ;; of sizing, etc.
       :rule-classes ((:rewrite :backchain-limit-lst 1)))))

(defun dts-member-implies-sum-thms (name prodinfos)
  (if (atom prodinfos)
      nil
    (cons (dts-member-implies-sum-thm name (car prodinfos))
          (dts-member-implies-sum-thms name (cdr prodinfos)))))

#||
(dts-member-implies-sum-thms 'mysum *prodinfos*)
||#

(defun dts-by-tag-thm (name prodinfo)

  ;; This produces theorems like this:
  ;; (defthm vl-constint-p-by-tag-when-vl-atomguts-p
  ;;   (implies (and (equal (tag x) :vl-constint)
  ;;                 (vl-atomguts-p x))
  ;;            (vl-constint-p x)))

  (b* ((xvar     (dts-x name))
       (sum-name (dts-recognizer-name name))
       (mem-name (fty::prodinfo->foop prodinfo))
       (mem-tag  (fty::prodinfo->tag prodinfo))
       (thm-name (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name mem-name)
                               "-BY-TAG-WHEN-"
                               (symbol-name sum-name))
                  name)))
    `(defthm ,thm-name
       (implies (and (equal (tag ,xvar) ,mem-tag)
                     (,sum-name ,xvar))
                (,mem-name ,xvar)))))

(defun dts-by-tag-thms (name prodinfos)
  (if (atom prodinfos)
      nil
    (cons (dts-by-tag-thm name (car prodinfos))
          (dts-by-tag-thms name (cdr prodinfos)))))

#||
(dts-by-tag-thms 'mysum *prodinfos*)
||#


(defun dts-when-invalid-tag-hyps (name prodinfos)
  (b* (((when (atom prodinfos))
        nil)
       (xvar (dts-x name))
       (tag  (fty::prodinfo->tag (car prodinfos))))
    (cons `(not (equal (tag ,xvar) ,tag))
          (dts-when-invalid-tag-hyps name (cdr prodinfos)))))

(defun dts-when-invalid-tag-thm (name prodinfos)
  ;; Generates a theorem like:
  ;; (defthm vl-atomicstmt-p-when-invalid-tag
  ;;   (implies (and (not (equal (tag x) :vl-nullstmt))
  ;;                 (not (equal (tag x) :vl-assignstmt))
  ;;                 (not (equal (tag x) :vl-deassignstmt))
  ;;                 (not (equal (tag x) :vl-enablestmt))
  ;;                 (not (equal (tag x) :vl-disablestmt))
  ;;                 (not (equal (tag x) :vl-eventtriggerstmt)))
  ;;          (not (vl-atomicstmt-p x)))
  ;;   :rule-classes ((:rewrite :backchain-limit-lst 0)))
  (b* ((xvar     (dts-x name))
       (sum-name (dts-recognizer-name name))
       (thm-name (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name sum-name)
                               "-WHEN-INVALID-TAG")
                  name)))
    `(defthm ,thm-name
       (implies (and . ,(dts-when-invalid-tag-hyps name prodinfos))
                (not (,sum-name ,xvar)))
       :rule-classes ((:rewrite :backchain-limit-lst 0)))))

#||
(dts-when-invalid-tag-thm 'mysum *prodinfos*)
||#




; ----------------------- Fixing Function --------------------------------------

(defun dts-fix-def (name prodinfos)
  (b* (((when (atom prodinfos))
        (er hard? 'deftranssum "Can't define transparent sum ~x0 with no member types." name))
       (info1   (car prodinfos))
       (mem-fix (fty::prodinfo->foo-fix info1))
       (sum-fix (dts-fix-name name))
       (sum-p   (dts-recognizer-name name))
       (xvar    (dts-x name)))
    `(defund-inline ,sum-fix (,xvar)
       (declare (xargs :guard (,sum-p ,xvar)))
       (mbe :logic (if (,sum-p ,xvar)
                       ,xvar
                     (,mem-fix ,xvar))
            :exec ,xvar))))

(defun dts-fix-thms (name)
  (b* ((sum-fix (dts-fix-name name))
       (sum-p   (dts-recognizer-name name))
       (xvar    (dts-x name)))
    `((defthm ,(intern-in-package-of-symbol
                (concatenate 'string (symbol-name sum-fix) "-WHEN-" (symbol-name sum-p))
                name)
        (implies (,sum-p ,xvar)
                 (equal (,sum-fix ,xvar)
                        ,xvar)))

      (defthm ,(intern-in-package-of-symbol
                (concatenate 'string (symbol-name sum-p) "-OF-" (symbol-name sum-fix))
                name)
        (,sum-p (,sum-fix ,xvar))))))

#||
(dts-fix-def 'mysum *prodinfos*)
(dts-fix-thms 'mysum)
||#


(defun deftranssum-fn (name other-args kwd-alist other-events state)
  (b* ((__function__ 'deftranssum)
       (?mksym-package-symbol name)

       (short (std::getarg :short nil kwd-alist))
       (long  (std::getarg :long nil kwd-alist))
       (mode  (std::getarg :mode (default-defun-mode (w state)) kwd-alist))

       (parents-p (assoc :parents kwd-alist))
       (parents   (cdr parents-p))
       (parents   (if parents-p
                      parents
                    (or (xdoc::get-default-parents (w state))
                        '(acl2::undocumented))))

       ((unless (or (eq mode :logic)
                    (eq mode :program)))
        (raise ":mode must be one of :logic or :program, but is ~x0." mode))
       ((unless (or (not short)
                    (stringp short)))
        (raise ":short must be a string or nil, but is ~x0." short))
       ((unless (or (not long)
                    (stringp long)))
        (raise ":long must be a string or nil, but is ~x0." long))

       (long (or long
                 (and parents
                      "<p>This is an ordinary @(see vl::deftranssum) of aggregates.</p>")))

       ((unless (std::tuplep 1 other-args))
        (raise "deftranssum should be given exactly one non-keyword argument, but got ~x0"
               other-args))

       (foo-p     (dts-recognizer-name name))
       (foo-fix   (dts-fix-name name))
       (foo-equiv (dts-equiv-name name))
       (x         (dts-x name))

       (prodnames (first other-args))
       (prodinfos (fty::get-flexprod-infos prodnames (w state)))
       (def       (dts-recognizer-def name prodinfos))
       (fix-def   (dts-fix-def name prodinfos))

       ((when (eq mode :program))
        `(defsection ,foo-p
           ,@(and parents `(:parents ,parents))
           ,@(and short   `(:short ,short))
           ,@(and long    `(:long ,long))
           (program)
           ,def
           ,fix-def
           . ,other-events))

       (events
        `((logic)
          ,def
          (local (in-theory (enable ,foo-p)))

          ,fix-def
          (local (in-theory (enable ,foo-fix)))

          (defthm ,(mksym 'consp-when- foo-p)
            (implies (,foo-p ,x)
                     (consp ,x))
            :rule-classes :compound-recognizer)

          ,@(dts-member-implies-sum-thms name prodinfos)
          ,@(dts-by-tag-thms name prodinfos)
          ,(dts-when-invalid-tag-thm name prodinfos)
          ,@(dts-fix-thms name)

          (fty::deffixtype name
            :pred  ,foo-p
            :equiv ,foo-equiv
            :fix   ,foo-fix
            :define t
            :forward t)
          ;; BOZO maybe generate fast functions?
          ;; BOZO some kind of pattern-match macros?
          )))

    `(defsection ,foo-p
       ,@(and parents `(:parents ,parents))
       ,@(and short   `(:short ,short))
       ,@(and long    `(:long ,long))
       (encapsulate () . ,events)
       . ,other-events)))

(defmacro deftranssum (name &rest args)
  (b* ((__function__ 'deftranssum)
       ((unless (symbolp name))
        (raise "Name must be a symbol."))
       (ctx (list 'deftranssum name))
       ((mv main-stuff other-events) (std::split-/// ctx args))
       ((mv kwd-alist other-args)
        (std::extract-keywords ctx *deftranssum-valid-keywords* main-stuff nil)))
    ;; BOZO Add with-output stuff eventually
    `(make-event
      `(progn ,(deftranssum-fn ',name ',other-args ',kwd-alist ',other-events state)
              (value-triple '(deftranssum ,',name))))))

#||
(deftranssum mysum
  :mode :logic
  (foo bar baz))
||#

