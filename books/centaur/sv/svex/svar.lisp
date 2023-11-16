; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2023 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))

; Representation of variables in SV.

; Most optimized: simple string/non-Boolean symbol --
;   just a name, no properties, no delay, all bits 0

; Next most optimized: (:var name . int)
;  - Int encodes possible delay of 4 bits or less, then other bits
;  - No properties

; Next (:var name delay . bits)
;  - Only if delay is more than 4 bits
;  - No properties

; Finally (:var name (:delay . delay) (:bits . bits) . props)
;  - Most explicit

; Property list part is alist with symbol keys, arbitrary values

(fty::defmap svar-proplist :key-type symbol :true-listp t)


(local (defthm <-16-when-unsigned-byte-p
         (implies (unsigned-byte-p 4 x)
                  (< x 16))
         :hints(("Goal" :in-theory (enable unsigned-byte-p)))))

(local (defthm left-shift-equal-0
         (implies (natp sh)
                  (equal (equal (ash x sh) 0)
                         (equal (ifix x) 0)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(local (defthm logapp-equal-0
         (equal (equal (logapp n x y) 0)
                (and (equal (loghead n x) 0)
                     (equal (ifix y) 0)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(local (defthm logtail-not-equal-0
         (implies (and (not (equal 0 (ifix x)))
                       (equal 0 (loghead n x)))
                  (not (equal 0 (logtail n x))))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(local (defthm ash-logtail-when-loghead-0
         (implies (and (equal 0 (loghead n x))
                       (natp n))
                  (equal (Ash (logtail n x) n)
                         (ifix x)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs
                                            bitops::equal-logcons-strong)))))

(defflexsum svar
  :parents (svex)
  :kind nil
  (:svar
   :short "A single variable in a symbolic vector expression."
   :type-name svar
   :cond t
   :shape (if (atom x)
              (or (stringp x)
                  (and (symbolp x)
                       (not (booleanp x))))
            (and (eq (car x) :var)
                 (consp (cdr x))
                 (let* ((name (cadr x))
                        (rest (cddr x)))
                   (or (and (integerp rest)     ;; (:var name . int)
                            (or (not (or (stringp name)
                                         (and (symbolp name)
                                              (not (booleanp name)))))
                                (not (eql 0 rest))))
                       (and (consp rest)
                            (or (and (natp (car rest))    ;; (:var name delay . bits)
                                     (>= (car rest) 16)
                                     (integerp (cdr rest)))
                                (and (consp (first rest))
                                     (eq (car (first rest)) :delay)
                                     (natp (cdr (first rest)))

                                     (consp (cdr rest))
                                     (consp (second rest))
                                     (eq (car (second rest)) :bits)
                                     (integerp (cdr (second rest) ))

                                     (consp (cddr rest)) ;; props nonempty
                                     ;; (: var name (:delay . delay) (:bits . bits) . props)
                                     )))))))
   :fields
   ((name :acc-body (if (atom x)
                        x
                      (cadr x))
          :doc "The name of this variable.  This can be any ACL2 object at all,
                but our representation is optimized for @(see stringp) or @(see
                symbolp) names.")
    (delay :type natp
           :acc-body (if (atom x)
                         0
                       (b* ((rest (cddr x))
                            ((when (integerp rest)) (loghead 4 rest))
                            ((when (integerp (first rest))) (first rest)))
                         (cdr (first rest))))
           :default 0
           :doc "A natural valued index for this variable, used for instance
                 to support the encoding of, e.g., previous versus current
                 register values in FSMs.  The default delay (which enjoys an
                 optimized representation) is 0.  See below for some motivation
                 and explanation.")
    (bits :type integerp
          :acc-body (if (atom x)
                         0
                       (b* ((rest (cddr x))
                            ((when (integerp rest)) (logtail 4 rest))
                            ((when (integerp (first rest))) (cdr rest)))
                         (cdr (second rest))))
          :default 0
          :doc "An integer valued field used to record various bits of
                information. Often used to rename a set of variables to
                variables-prime, where we know the first set has certain bits
                unset.  Exact use varies over the phase of processing; e.g.,
                this is used to record the nonblocking bit for VL statement
                processing and used to record the override-test and
                override-val bits for SVTV processing.")
    (props :type svar-proplist
           :acc-body (if (atom x)
                         nil
                       (b* ((rest (cddr x))
                            ((when (integerp rest)) nil)
                            ((when (integerp (first rest))) nil))
                         (cddr rest)))
           :default nil
           :doc "An area to store any pieces of information that don't fit in
                 the bits.  This can be any alist mapping symbols to arbitrary
                 values."))
   :ctor-body
   (cond (props
          (hons :var
                (hons name
                      (hons (hons :delay delay)
                            (hons (hons :bits bits)
                                  props)))))
         ((>= delay 16)
          (hons :var (hons name (hons delay bits))))
         ((and (or (stringp name)
                   (and (symbolp name)
                        (not (booleanp name))))
               (eql delay 0)
               (eql bits 0))
          name)
         (t (hons :var (hons name (logapp 4 delay bits)))))
   :long "<p>Each variable in an @(see svex) represents a @(see 4vec).</p>

<p>In most s-expression formats, e.g., s-expressions in Lisp or in the @(see
acl2::4v-sexprs) used in @(see acl2::esim), a variable is just a symbol, which
is generally treated as if it were an atomic <b>name</b> with no further
structure.</p>

<p>In contrast, in @(see sv), our variables have both a name and also a natural
numbered index (called @('delay')).  This index is mainly an implementation
detail that allows us to cheaply (i.e., without @(see intern$)) construct new
variables.</p>

<p>In the semantics of expressions, e.g., in @(see svex-lookup), variables are
distinct whenever they differ by name <b>or</b> by delay.  That is, as far as
expression evaluation is concerned, the variable named \"v\" with delay 5 is
completely distinct from \"v\" with delay 4.  Think of them as you would
indexed variables like @($v_5$) versus @($v_4$) in some mathematics.</p>")
  
  ;; :prepwork ((local (defthm logbitp-open
  ;;                     (implies (syntaxp (quotep n))
  ;;                              (equal (logbitp n x)
  ;;                                     (cond ((zp n) (bit->bool (logcar x)))
  ;;                                           (t (logbitp (1- n) (logcdr x))))))
  ;;                     :hints(("Goal" :in-theory (enable bitops::logbitp**)))))

  ;;            (local (defthm loghead-open
  ;;                     (implies (syntaxp (quotep n))
  ;;                              (equal (loghead n x)
  ;;                                     (cond ((zp n) 0)
  ;;                                           (t (logcons (logcar x) (loghead (1- n) (logcdr x)))))))
  ;;                     :hints(("Goal" :in-theory (enable bitops::loghead**)))))

  ;;            (local (defthm logtail-open
  ;;                     (implies (syntaxp (quotep n))
  ;;                              (equal (logtail n x)
  ;;                                     (cond ((zp n) (ifix x))
  ;;                                           (t (logtail (1- n) (logcdr x))))))
  ;;                     :hints(("Goal" :in-theory (enable bitops::logtail**)))))

  ;;            ;; (local (in-theory (enable bitops::equal-logcons-strong)))
  ;;            ;; (local (defthm equal-of-cons
  ;;            ;;          (equal (equal (cons a b) c)
  ;;            ;;                 (and (consp c)
  ;;            ;;                      (equal a (car c))
  ;;            ;;                      (equal b (cdr c))))))
  ;;            (local (in-theory (disable default-car default-cdr
  ;;                                       bitops::logcons-posp-2
  ;;                                       bitops::logcons-posp-1
  ;;                                       acl2::natp-when-gte-0))))
  )
