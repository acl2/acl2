; Copyright (C) Intel Corporation
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

; Rewrite and simplify terms using the proof builder's rewriter. This file is
; based on 'books/tools/easy-simplify'.

; Some helpful lemmas for reducing terms that may be encountered in
; SVTV-related terms.

(in-package "SV")

(include-book "centaur/sv/svex/4vec" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(include-book "std/lists/take" :dir :system)

; SV-related lemmas

(defthmd 4vec-p-when-integerp-hyp
  (implies (integerp x)
           (sv::4vec-p x))
  :rule-classes :type-prescription
  :hints (("goal" :in-theory (e/d (sv::4vec-p) nil))))

(defthmd 2vec-when-integerp
  (implies (integerp x)
           (equal (sv::2vec x) x))
  :hints (("Goal" :in-theory (enable sv::4vec->upper
                                     sv::4vec->lower))))

(defthmd 4vec->upper-when-integerp
  (implies (integerp x)
           (equal (sv::4vec->upper x) x))
  :hints
  (("Goal" :in-theory (enable sv::4vec->upper))))

(defthmd 4vec->lower-when-integerp
  (implies (integerp x)
           (equal (sv::4vec->lower x) x))
  :hints
  (("Goal" :in-theory (enable sv::4vec->lower))))

(defthmd 4vec-zero-ext-when-natp
  (implies (and (integerp x)
		(natp n))
	   (equal (sv::4vec-zero-ext n x)
		  (loghead n x)))
  :hints
  (("Goal" :in-theory
    (e/d (sv::4vec-zero-ext sv::4vec->upper sv::4vec->lower)
         (loghead)))))

; CONS-related lemmas

(defthmd len-of-cons
  (equal (len (cons a b))
         (+ 1 (len b)))
  :hints (("Goal" :in-theory (enable len))))

(defthmd nthcdr-of-cons
  (equal (nthcdr n (cons a l))
         (if (zp n)
             (cons a l)
           (nthcdr (1- n) l))))

(deftheory e-smpl-theory
; The theory that will be used for rewriting
  `(
; same basic rules
    minimal-theory
    acl2::natp-compound-recognizer
    acl2::ifix-when-integerp
    acl2::nfix-when-natp
    acl2::bfix-when-bitp
    acl2::unsigned-byte-p-forward-to-nonnegative-integerp
    acl2::take-of-cons
    acl2::lifix$inline
    len-of-cons
    acl2::loghead-type
    nthcdr-of-cons
; cons-car-cdr rules
    cdr-cons car-cons
; some SV/bit-manupulation-related rules
    sv::4vec-fix$inline
    sv::4vec-fix-of-4vec
    4vec-p-when-integerp
    4vec->lower-when-integerp
    4vec->upper-when-integerp
    2vec-when-integerp
    4vec-zero-ext-when-natp
    ))

(defmacro e-smpl (term hyps-type-alist rcnst)
  ; Call the proof builder rewriter in a restricted manner.
  `(b* (((mv ?step-limit new-term ?new-ttree state)
	 (acl2::pc-rewrite*
	  ,term
	  ,hyps-type-alist
	  nil                           ; geneqv
	  nil                           ; iff-flg
	  (w state)
	  ,rcnst
	  nil                           ; old-ttree
	  nil                           ; pot-lst
	  nil				; normalize-flg
	  t				; rewrite-flg
	  nil                           ; ens, only needed if normalize 't
	  state
	  1000				; repeat
	  1000				; backchain-limit
          (acl2::initial-step-limit (w state) state)
          )))
     (value new-term)))

(define load-hints-into-rcnst (hints
                               base-rcnst
                               &key
                               (state 'state))
  :mode :program
  (b* ((world (w state))
       ((er hint-settings)
        (acl2::translate-hint-settings
         'simp-term "Goal" hints 'get-hyps-type-alist-rcnst world state))
       ((er rcnst)
        (acl2::load-hint-settings-into-rcnst
         hint-settings base-rcnst
         :easy-simplify
         world 'get-hyps-type-alist-rcnst state)))
    (value rcnst)))

(define get-hyps-type-alist-rcnst (hyps hints state)
; Based on easy-simplify-term's process of converting hyps and hints for the
; rewriter to use. The results of this function can be passed into e-smpl.
  :mode :program
  (b* ((world (w state))
; Convert hints for rewriter
       (ens (acl2::ens state))
       (base-rcnst
        (change acl2::rewrite-constant
                acl2::*empty-rewrite-constant*
                :current-enabled-structure ens
                :force-info t))
       ((mv - rcnst state)
        (load-hints-into-rcnst hints base-rcnst))
; Convert hyps for rewriter
       (ens (access acl2::rewrite-constant rcnst :current-enabled-structure))
       ((er trans-hyp-term)
        (acl2::translate hyps t nil t 'get-hyps-type-alist-rcnst world state))
       (hyps (acl2::expand-assumptions-1 trans-hyp-term))
       ((mv flg hyps-type-alist ?ttree)
        (acl2::hyps-type-alist hyps ens world state))
       ((when flg)
        (mv "Contradiction in the hypotheses"
            nil state)))
    (mv hyps-type-alist rcnst state)))

; A note on pc-rewrite*
#||

pc-rewrite* takes the following arguments:

term:
-----

A translated term.

type-alist:
-----------

The rewrite lemmas for the hypotheses/assumptions needed for the term.

geneqv:
-------

Not used.

iff-flg:
--------

Option used if normalizing

wrld:
-----

The world

rcnst:
------

The Rewriter's ``Constant Argument''

A record of "constants" used by the rewriter. Includes the constant
"CURRENT-ENABLED-STRUCTURE", which is a "parent tree" that contains the theory
which specifies the rules that are enabled.

old-ttree:
----------

ttree is a tag-tree. Contains useful info such as the lemmas used, linearize
assumptions made, etc.

pot-lst:
--------

Set of "polynomials".

normalize-flg:
--------------

Whether to normalize the term.

rewrite-flg:
------------

Whether to rewrite the term.

ens:
----

The global enabled-structure

state:
------

STATE

repeat:
-------

How many times to repeat applying the rewriter, if each application generates a
new term.

backchain-limit:
----------------

Not used.

step-limit:
-----------

||#
