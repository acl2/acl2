; ACL2 Standard Library
; Copyright (c) 2008-2015 Centaur Technology
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
(include-book "defaggregate")
(include-book "deflist")
(set-state-ok t)
(program)

(defxdoc defsum
  :parents (std/util)
  :short "(Beta) Introduce a tagged union data type, also commonly called a
variant or sum type."

  :long "<box><p>Note: Defsum is currently under development.  You are welcome
to use it, but please be advised that we may drastically change its interface
and implementation.</p></box>

<h3>Introduction</h3>

<p><b>Defsum</b> is a macro that automates introducing a recognizer,
pattern-binding macro, and certain supporting theorems for new <a
href='https://en.wikipedia.org/wiki/Tagged_union'>tagged union</a> data
types.</p>

<p>Defsum is currently restricted to unions of tagged aggregates, which must be
introduced ahead of time using @(see defaggregate), and does not currently
support mutual recursive data types.  (In the future we may work to lift these
restrictions).</p>")

(defconst *defsum-valid-keywords*
  '(:mode
    :parents
    :short
    :long
    ))

#|| ;; For testing
(encapsulate
  ()
  (logic)
  (defaggregate foo :tag :foo (a b c))
  (defaggregate bar :tag :bar (x y z))
  (defaggregate baz :tag :baz (w)))

||#

(defun ds-find-aggregates
  (names         ;; aggregate names, e.g., (FOO BAR) for (defaggregate foo ...) (defaggregate bar ...)
   agginfo-alist ;; alist of name -> agginfo returned by get-aggregates
   )
  ;; Returns a list of agginfo structures
  (b* (((when (atom names))
        nil)
       ((cons name rest) names)
       (look (assoc name agginfo-alist))
       ((unless look)
        (er hard? 'ds-find-aggregates
            "Aggregate ~x0 not found; has it been defined with defaggregate?"
            name)))
    (cons (cdr look)
          (ds-find-aggregates rest agginfo-alist))))

#||
(make-event
 `(defconst *agginfos*
    ',(ds-find-aggregates '(foo bar baz) (get-aggregates (w state)))))
||#

(defun ds-x (basename)
  (intern-in-package-of-symbol "X" basename))

(defun ds-recognizer-name (basename)
  (intern-in-package-of-symbol (concatenate 'string (symbol-name basename) "-P")
                               basename))

(defun ds-recognizer-logic-def-aux (agginfos xvar)
  (if (atom agginfos)
      nil
    (cons `(,(da-recognizer-name (agginfo->name (car agginfos))
                                 (agginfo->pred (car agginfos))) ,xvar)
          (ds-recognizer-logic-def-aux (cdr agginfos) xvar))))

(defun ds-recognizer-logic-def (name agginfos)
  (cons 'or
        (ds-recognizer-logic-def-aux agginfos (ds-x name))))

#||
(ds-recognizer-logic-def 'mysum *agginfos*)
||#

(defun ds-recognizer-exec-def-aux (agginfos xvar)
  (cond ((atom agginfos)
         nil)
        ((atom (cdr agginfos))
         ;; last one, just use "otherwise"
         `((otherwise
            (,(da-recognizer-name (agginfo->name (car agginfos))
                                  (agginfo->pred (car agginfos))) ,xvar))))
        (t
         (cons `(,(agginfo->tag (car agginfos))
                 (,(da-recognizer-name (agginfo->name (car agginfos))
                                       (agginfo->pred (car agginfos))) ,xvar))
               (ds-recognizer-exec-def-aux (cdr agginfos) xvar)))))

(defun ds-recognizer-exec-def (name agginfos)
  (let ((xvar (ds-x name)))
    `(case (tag ,xvar)
       . ,(ds-recognizer-exec-def-aux agginfos xvar))))

#||
(ds-recognizer-exec-def 'mysum *agginfos*)
||#

(defun ds-recognizer-def (name agginfos)
  (let ((xvar (ds-x name)))
    `(defund ,(ds-recognizer-name name) (,xvar)
       (declare (xargs :guard t))
       (mbe :logic ,(ds-recognizer-logic-def name agginfos)
            :exec ,(ds-recognizer-exec-def name agginfos)))))

#||
(ds-recognizer-def 'mysum *agginfos*)
||#


(defun ds-member-implies-sum-thm (name agginfo)

  ;; This produces theorems like this:
  ;; (defthm vl-atomguts-p-when-vl-constint-p
  ;;   (implies (vl-constint-p x)
  ;;            (vl-atomguts-p x)))

  (b* ((xvar     (ds-x name))
       (sum-name (ds-recognizer-name name))
       ((agginfo agginfo) agginfo)
       (mem-name (da-recognizer-name agginfo.name agginfo.pred))
       (thm-name (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name sum-name) "-WHEN-"
                               (symbol-name mem-name))
                  name)))
    `(defthm ,thm-name
       (implies (,mem-name ,xvar)
                (,sum-name ,xvar)))))

(defun ds-member-implies-sum-thms (name agginfos)
  (if (atom agginfos)
      nil
    (cons (ds-member-implies-sum-thm name (car agginfos))
          (ds-member-implies-sum-thms name (cdr agginfos)))))

#||
(ds-member-implies-sum-thms 'mysum *agginfos*)
||#

(defun ds-by-tag-thm (name agginfo)

  ;; This produces theorems like this:
  ;; (defthm vl-constint-p-by-tag-when-vl-atomguts-p
  ;;   (implies (and (equal (tag x) :vl-constint)
  ;;                 (vl-atomguts-p x))
  ;;            (vl-constint-p x)))

  (b* ((xvar     (ds-x name))
       (sum-name (ds-recognizer-name name))
       ((agginfo agginfo) agginfo)
       (mem-name (da-recognizer-name agginfo.name agginfo.pred))
       (thm-name (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name mem-name)
                               "-BY-TAG-WHEN-"
                               (symbol-name sum-name))
                  name)))
    `(defthm ,thm-name
       (implies (and (equal (tag ,xvar) ,agginfo.tag)
                     (,sum-name ,xvar))
                (,mem-name ,xvar)))))

(defun ds-by-tag-thms (name agginfos)
  (if (atom agginfos)
      nil
    (cons (ds-by-tag-thm name (car agginfos))
          (ds-by-tag-thms name (cdr agginfos)))))

#||
(ds-by-tag-thms 'mysum *agginfos*)
||#


(defun ds-when-invalid-tag-hyps (name agginfos)
  (b* (((when (atom agginfos))
        nil)
       (xvar (ds-x name))
       ((agginfo agginfo) (car agginfos)))
    (cons `(not (equal (tag ,xvar) ,agginfo.tag))
          (ds-when-invalid-tag-hyps name (cdr agginfos)))))

(defun ds-when-invalid-tag-thm (name agginfos)
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
  (b* ((xvar     (ds-x name))
       (sum-name (ds-recognizer-name name))
       (thm-name (intern-in-package-of-symbol
                  (concatenate 'string (symbol-name sum-name)
                               "-WHEN-INVALID-TAG")
                  name)))
    `(defthm ,thm-name
       (implies (and . ,(ds-when-invalid-tag-hyps name agginfos))
                (not (,sum-name ,xvar)))
       :rule-classes ((:rewrite :backchain-limit-lst 0)))))

#||
(ds-when-invalid-tag-thm 'mysum *agginfos*)
||#

(defun defsum-fn (name other-args kwd-alist other-events state)
  (b* ((__function__ 'deflist)
       (?mksym-package-symbol name)

       (short (getarg :short nil kwd-alist))
       (long  (getarg :long nil kwd-alist))
       (mode  (getarg :mode (default-defun-mode (w state)) kwd-alist))

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
                      "<p>This is an ordinary @(see std::defsum) of aggregates.</p>")))

       ((unless (tuplep 1 other-args))
        (raise "defsum should be given exactly one non-keyword argument, but got ~x0"
               other-args))

       (aggnames (first other-args))
       (agginfos (ds-find-aggregates aggnames (get-aggregates (w state))))
       (def      (ds-recognizer-def name agginfos))
       (name-p   (ds-recognizer-name name))
       (x        (ds-x name))

       ((when (eq mode :program))
        `(defsection ,name
           ,@(and parents `(:parents ,parents))
           ,@(and short   `(:short ,short))
           ,@(and long    `(:long ,long))
           (program)
           ,def
           . ,other-events))

       (events
        `((logic)
          ,def
           (local (in-theory (enable ,name-p)))

          (defthm ,(mksym 'consp-when- name-p)
            (implies (,name-p ,x)
                     (consp ,x))
            :rule-classes :compound-recognizer)

          ,@(ds-member-implies-sum-thms name agginfos)
          ,@(ds-by-tag-thms name agginfos)
          ,(ds-when-invalid-tag-thm name agginfos)

          ;; BOZO maybe generate fast functions?
          ;; BOZO some kind of pattern-match macros?
          )))

    `(defsection ,name
       ,@(and parents `(:parents ,parents))
       ,@(and short   `(:short ,short))
       ,@(and long    `(:long ,long))
       (encapsulate () . ,events)
       . ,other-events)))

(defmacro defsum (name &rest args)
  (b* ((__function__ 'defsum)
       ((unless (symbolp name))
        (raise "Name must be a symbol."))
       (ctx (list 'defsum name))
       ((mv main-stuff other-events) (split-/// ctx args))
       ((mv kwd-alist other-args)
        (extract-keywords ctx *defsum-valid-keywords* main-stuff nil)))
    ;; BOZO Add with-output stuff eventually
    `(make-event
      `(progn ,(defsum-fn ',name ',other-args ',kwd-alist ',other-events state)
              (value-triple '(defsum ,',name))))))

#||
(defsum mysum
  :mode :logic
  (foo bar baz))
||#
