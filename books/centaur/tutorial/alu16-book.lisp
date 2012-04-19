; Centaur Hardware Verification Tutorial
; Copyright (C) 2012 Centaur Technology
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


; alu16-book.lisp
;
; This file is a cleaned up version of alu16.lsp which is a certifiable ACL2
; book.
;
; This file has no comments to explain what is happening.  If you are just
; starting the tutorial, please start with alu16.lsp instead; it contains lots
; of explanation and also covers other interactive/debugging features.
;
; I don't do the full multiplier proof here, but instead only prove it
; multiplies when the arguments are under 2^8.  This lets this file be
; certified in a reasonable amount of time, even on a modest machine.

(in-package "ACL2")
(include-book "intro")
(value-triple (set-max-mem (* 3 (expt 2 30))))

(defmodules *translation*
  :start-files (list "alu16.v"))

(defconst *alu16*
  (b* ((mods  (vl::vl-translation->mods *translation*))
       (alu16 (vl::vl-find-module "alu16" mods))
       ((unless alu16)
        (er hard? '*alu16* "Failed to translate alu16?"))
       (esim  (vl::vl-module->esim alu16))
       ((unless (good-esim-modulep esim))
        (er hard? '*alu16* "Failed to produce a good esim module")))
    esim))

(defstv *test-vector*
  :mod *alu16*
  :inputs '(("opcode" op)
            ("abus"   a)
            ("bbus"   b))
  :outputs '(("out"    res)))

;; (defconst *op-plus*    0)
;; (defconst *op-minus*   1)
;; (defconst *op-bitand*  2)
;; (defconst *op-bitor*   3)
;; (defconst *op-bitxor*  4)
;; (defconst *op-min*     5)
;; (defconst *op-count*   6)
;; (defconst *op-mult*    7)

;; (defun vecp (n x)
;;   (and (natp x)
;;        (<= 0 x)
;;        (< x (expt 2 n))))

;; (defmacro alu16-type-hyps ()
;;   `(and (vecp 3 op)
;;         (vecp 16 a)
;;         (vecp 16 b)))

;; (defmacro alu16-default-bindings ()
;;   `(gl::auto-bindings (:nat op 3)
;;                       (:mix (:nat a 16)
;;                             (:nat b 16))))

;; (defmacro alu16-basic-result ()
;;   `(let* ((in-alist (list (cons 'op op)
;;                           (cons 'a  a)
;;                           (cons 'b  b)))
;;           (out-alist (stv-run *test-vector* in-alist))
;;           (res       (cdr (assoc 'res out-alist))))
;;      res))

;; (defmacro alu16-thm (name &key opcode spec (g-bindings '(alu16-default-bindings)))
;;   `(def-gl-thm ,name
;;      :hyp (and (alu16-type-hyps)
;;                (equal op ,opcode))
;;      :concl (equal (alu16-basic-result) ,spec)
;;      :g-bindings ,g-bindings))

;; (alu16-thm alu16-plus-correct
;;            :opcode *op-plus*
;;            :spec (mod (+ a b) (expt 2 16)))

;; (alu16-thm alu16-minus-correct
;;            :opcode *op-minus*
;;            :spec (mod (- a b) (expt 2 16)))

;; (alu16-thm alu16-bitand-correct
;;            :opcode *op-bitand*
;;            :spec (logand a b))

;; (alu16-thm alu16-bitor-correct
;;            :opcode *op-bitor*
;;            :spec (logior a b))

;; (alu16-thm alu16-bitxor-correct
;;            :opcode *op-bitxor*
;;            :spec (logxor a b))

;; (alu16-thm alu16-min-correct
;;            :opcode *op-min*
;;            :spec (min a b))


;; (defun buggy-logcount (a)
;;   (+ (logbit 0 a)
;;      (logbit 1 a)
;;      (logbit 2 a)
;;      (logbit 3 a)
;;      (logbit 4 a)
;;      (logbit 5 a)
;;      (logbit 6 a)
;;      (logbit 3 a) ;; <-- 3 instead of 7
;;      (logbit 8 a)
;;      (logbit 9 a)
;;      (logbit 10 a)
;;      (logbit 11 a)
;;      (logbit 12 a)
;;      (logbit 13 a)
;;      (logbit 14 a)
;;      (logbit 15 a)))

;; (alu16-thm alu16-count-buggy
;;            :opcode *op-count*
;;            :spec (buggy-logcount a))

;; (def-gl-thm alu16-mult-partially-correct
;;   :hyp (and (alu16-type-hyps)
;;             (equal op *op-mult*)
;;             (< a (expt 2 8))
;;             (< b (expt 2 8)))
;;   :concl (equal (alu16-basic-result)
;;                 (mod (* a b) (expt 2 16)))
;;   :g-bindings (alu16-default-bindings))
