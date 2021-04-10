; Copyright (C) 2020, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "GL")

; Matt K. mod: Avoid ACL2(p) error from a clause-processor that returns one or
; more stobjs.
(set-waterfall-parallelism nil)

; this book is just a standard GL-setup book including the relevant
; GL and SV books and rebuilding the clause-processor to get g-aig-eval:

;; First, let's load up some additional satlink/aignet/svex definitions to help with
;; GL processing of RTL definitions (in particular, we need symbolic version of
;; svexlist-eval for processing svtv's from RTL efficiently):

(include-book "centaur/satlink/top" :dir :system)
(include-book "centaur/aignet/top" :dir :system)
(include-book "centaur/sv/svex/top" :dir :system)

;; Now, let's go ahead and load up GL and add the g-aig-eval mapping of aig-eval-list
;; to the current clause-processor:

(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/gl/bfr-aig-bddify" :dir :system)
(include-book "centaur/gl/bfr-satlink" :dir :system)
(include-book "centaur/gl/gl-mbe" :dir :system)
(include-book "centaur/aig/g-aig-eval" :dir :system)

;; NOTE:: unfortunately our default glcp does NOT include the important g-aig-eval def-g-correct-thm :(...
;; so, we need to make our own glcp:
(acl2::def-gl-clause-processor my-glcp :output nil)

;; now we setup memory and satlink settings for GL through a macro
;; which can be used in books running GL stuff:
(defmacro init-gl-params ()
  `(progn
     (value-triple (acl2::tshell-start))
     (include-book "centaur/misc/memory-mgmt" :dir :system)
     (value-triple (hons-resize :addr-ht 2200000 :sbits 2200000))
     (value-triple (acl2::set-max-mem (* 50 (expt 2 30))))
     (defun my-satlink-config ()
       (declare (xargs :guard t))
       (satlink::make-config :cmdline "glucose -model"
                             :verbose t
                             :mintime 1))
     (defattach gl::gl-satlink-config
       my-satlink-config)
     (gl::gl-satlink-mode)
     (set-slow-alist-action :break)))



