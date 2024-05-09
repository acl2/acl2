
; Multiplier verification

; Copyright (C) 2022 Intel Corporation
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
; Original author: Mertcan Temel <mert.temel@intel.com>

(in-package "RP")

(include-book "../fnc-defs")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define some functions to help enable/disable some heuristics.

(progn
  ;; Whether the overall search should be more aggressive or not. This may help
  ;; find more adders, but also in some  cases, it may prevent the program from
  ;; finding adders.
  (encapsulate
    (((aggressive-find-adders-in-svex) => *))
    (local
     (defun aggressive-find-adders-in-svex ()
       nil)))

  (defmacro enable-aggressive-find-adders-in-svex (enable)
    (if enable
        `(defattach aggressive-find-adders-in-svex return-t)
      `(defattach aggressive-find-adders-in-svex return-nil)))

  (enable-aggressive-find-adders-in-svex nil))

(progn
  ;; Pick if the expressions after adder-detection  should be cleaned up a tiny
  ;; bit more.  merge-fa-chains will replace instances such as (fa-c-chain ...)
  ;; and (fa-s-chain  ...) with a full-adder  function. This may help  speed up
  ;; the proofs.
  (encapsulate
    (((merge-fa-chains) => *))
    (local
     (defun merge-fa-chains ()
       nil)))

  (defmacro enable-merge-fa-chains (enable)
    (if enable
        `(defattach merge-fa-chains return-t)
      `(defattach merge-fa-chains return-nil)))

  (enable-merge-fa-chains t))

(progn
  ;; For shifted multiplier cases, truncations  may prevent some patterns to be
  ;; detected. This heuristic  tries to put back a carry  pattern of half-adder
  ;; back without the usual checks. Enabled by default as no harm from this has
  ;; been observed.
  (encapsulate
    (((search-and-add-ha-c-for-shifted-enabled) => *))
    (local
     (defun search-and-add-ha-c-for-shifted-enabled ()
       nil)))

  (defmacro enable-search-and-add-ha-c-for-shifted (enable)
    (if enable
        `(defattach search-and-add-ha-c-for-shifted-enabled return-t)
      `(defattach search-and-add-ha-c-for-shifted-enabled return-nil)))

  (enable-search-and-add-ha-c-for-shifted t))

(progn
  ;; During pattern matching iterations,  global simplification function may be
  ;; called. This may help in some cases  but it is disabled by default because
  ;; it can also mess  up with the structure too much and  cause patterns to be
  ;; missed.
  (encapsulate
    (((find-adders-global-bitand/or/xor-simplification-enabled) => *))
    (local
     (defun find-adders-global-bitand/or/xor-simplification-enabled ()
       nil)))

  (defmacro enable-find-adders-global-bitand/or/xor-simplification (enable)
    (if enable
        `(defattach find-adders-global-bitand/or/xor-simplification-enabled return-t)
      `(defattach find-adders-global-bitand/or/xor-simplification-enabled return-nil)))

  (enable-find-adders-global-bitand/or/xor-simplification nil))

(progn
  ;; Probably not useful  for a lot of people. This  determines whether to keep
  ;; missing variables  in an svex environment  in the svex or  not.  When nil,
  ;; those missing variables will be dont-cares, otherwise their variable names
  ;; will stay in the svex.
  (encapsulate
    (((keep-missing-env-vars-in-svex) => *))
    (local
     (defun keep-missing-env-vars-in-svex ()
       nil)))

  (defmacro enable-keep-missing-env-vars-in-svex (enable)
    (if enable
        `(defattach keep-missing-env-vars-in-svex return-t)
      `(defattach keep-missing-env-vars-in-svex return-nil)))

  (enable-keep-missing-env-vars-in-svex nil))
