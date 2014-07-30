; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "assms-top")
(%interactive)


(%autoadmit hons-lookup)
(%autoadmit hons-update)
(%enable default hons-update hons-lookup)


(defsection rw.cachelinep
  (%autoadmit rw.cachelinep)
  (%autoadmit rw.cacheline)
  (%autoadmit rw.cacheline->eqltrace)
  (%autoadmit rw.cacheline->ifftrace)

  (local (%enable default
                  rw.cachelinep
                  rw.cacheline
                  rw.cacheline->eqltrace
                  rw.cacheline->ifftrace))

  (%autoprove booleanp-of-rw.cachelinep)
  (%autoprove forcing-rw.cachelinep-of-rw.cacheline)
  (%autoprove rw.cacheline->eqltrace-of-rw.cacheline)
  (%autoprove rw.cacheline->ifftrace-of-rw.cacheline)
  (%autoprove forcing-rw.tracep-of-rw.cacheline->eqltrace)
  (%autoprove forcing-rw.trace->iffp-of-rw.cacheline->eqltrace)
  (%autoprove forcing-rw.tracep-of-rw.cacheline->ifftrace)
  (%autoprove forcing-rw.trace->iffp-of-rw.cacheline->ifftrace))



(%deflist rw.cacheline-listp (x)
          (rw.cachelinep x))


(defsection rw.cacheline-assmsp
  (%autoadmit rw.cacheline-assmsp)
  (local (%enable default rw.cacheline-assmsp))
  (%autoprove booleanp-of-rw.cacheline-assmsp)
  (%autoprove forcing-rw.trace->assms-of-rw.cacheline->ifftrace)
  (%autoprove forcing-rw.trace->assms-of-rw.cacheline->eqltrace)
  (%autoprove forcing-rw.cacheline-assmsp-of-rw.cacheline))

(%deflist rw.cacheline-list-assmsp (x assms)
          (rw.cacheline-assmsp x assms))

(%autoprove rw.trace->assms-of-rw.cacheline->eqltrace-of-lookup
            (%cdr-induction data))

(%autoprove rw.trace->assms-of-rw.cacheline->ifftrace-of-lookup
            (%cdr-induction data))



(defsection rw.cacheline-traces-okp
  (%autoadmit rw.cacheline-traces-okp)
  (local (%enable default rw.cacheline-traces-okp))
  (%autoprove booleanp-of-rw.cacheline-traces-okp)
  (%autoprove forcing-rw.trace-okp-of-rw.cacheline->ifftrace)
  (%autoprove forcing-rw.trace-okp-of-rw.cacheline->eqltrace)
  (%autoprove forcing-rw.cacheline-traces-okp-of-rw.cacheline))

(%deflist rw.cacheline-list-traces-okp (x defs)
          (rw.cacheline-traces-okp x defs))

(%autoprove rw.trace-okp-of-rw.cacheline->eqltrace-of-lookup
            (%cdr-induction data)
            (%forcingp nil))

(%autoprove rw.trace-okp-of-rw.cacheline->ifftrace-of-lookup
            (%cdr-induction data)
            (%forcingp nil))



(defsection rw.cacheline-atblp
  (%autoadmit rw.cacheline-atblp)
  (local (%enable default rw.cacheline-atblp))
  (%autoprove booleanp-of-rw.cacheline-atblp)
  (%autoprove forcing-rw.trace-atblp-of-rw.cacheline->ifftrace)
  (%autoprove forcing-rw.trace-atblp-of-rw.cacheline->eqltrace)
  (%autoprove forcing-rw.cacheline-atblp-of-rw.cacheline))

(%deflist rw.cacheline-list-atblp (x atbl)
          (rw.cacheline-atblp x atbl))

(%autoprove rw.trace-atblp-of-rw.cacheline->eqltrace-of-lookup
            (%cdr-induction data)
            (%forcingp nil))

(%autoprove rw.trace-atblp-of-rw.cacheline->ifftrace-of-lookup
            (%cdr-induction data)
            (%forcingp nil))



(defsection rw.cacheline-env-okp
  (%autoadmit rw.cacheline-env-okp)
  (local (%enable default rw.cacheline-env-okp))
  (%autoprove booleanp-of-rw.cacheline-env-okp)
  (%autoprove forcing-rw.trace-env-okp-of-rw.cacheline->ifftrace)
  (%autoprove forcing-rw.trace-env-okp-of-rw.cacheline->eqltrace)
  (%autoprove forcing-rw.cacheline-env-okp-of-rw.cacheline))


(%deflist rw.cacheline-list-env-okp (x defs thms atbl)
          (rw.cacheline-env-okp x defs thms atbl))

(%autoprove rw.trace-env-okp-of-rw.cacheline->eqltrace-of-lookup
            (%cdr-induction data)
            (%forcingp nil))

(%autoprove rw.trace-env-okp-of-rw.cacheline->ifftrace-of-lookup
            (%cdr-induction data)
            (%forcingp nil))


(%defmap :map (rw.cachemapp x)
         :key (logic.termp x)
         :val (rw.cachelinep x)
         :key-list (logic.term-listp x)
         :val-list (rw.cacheline-listp x)
         :val-of-nil nil)



(defsection rw.cachemal-lhses-okp
  (%autoadmit rw.cachemap-lhses-okp)
  (%autoprove rw.cachemap-lhses-okp-when-not-consp
              (%restrict default rw.cachemap-lhses-okp (equal x 'x)))
  (%autoprove rw.cachemap-lhses-okp-of-cons
              (%restrict default rw.cachemap-lhses-okp (equal x '(cons a x))))
  (%autoprove booleanp-of-rw.cachemap-lhses-okp
              (%cdr-induction x))
  (%autoprove rw.trace->lhs-of-rw.cacheline->eqltrace-of-lookup
              (%cdr-induction data))
  (%autoprove rw.trace->lhs-of-rw.cacheline->ifftrace-of-lookup
              (%cdr-induction data)))



(%defaggregate rw.cache
               (blockp data)
               :require ((booleanp-of-rw.cache->blockp   (booleanp blockp))
                         (rw.cachemapp-of-rw.cache->data (rw.cachemapp data))))


(%autoadmit rw.cache-assmsp)
(%autoprove booleanp-of-rw.cache-assmsp
            (%enable default rw.cache-assmsp))

(%autoadmit rw.cache-traces-okp)
(%autoprove booleanp-of-rw.cache-traces-okp
            (%enable default rw.cache-traces-okp))

(%autoadmit rw.cache-atblp)
(%autoprove booleanp-of-rw.cache-atblp
            (%enable default rw.cache-atblp))

(%autoadmit rw.cache-env-okp)
(%autoprove booleanp-of-rw.cache-env-okp
            (%enable default rw.cache-env-okp))

(%autoadmit rw.cache-lhses-okp)
(%autoprove booleanp-of-rw.cache-lhses-okp
            (%enable default rw.cache-lhses-okp))


(defsection rw.set-blockedp
  (%autoadmit rw.set-blockedp)
  (%autoprove forcing-rw.cachep-of-rw.set-blockedp
              (%enable default rw.set-blockedp))
  (%autoprove forcing-rw.cache-assmsp-of-rw.set-blockedp
              (%enable default rw.set-blockedp rw.cache-assmsp))
  (%autoprove forcing-rw.cache-traces-okp-of-rw.set-blockedp
              (%enable default rw.set-blockedp rw.cache-traces-okp))
  (%autoprove forcing-rw.cache-atblp-of-rw.set-blockedp
              (%enable default rw.set-blockedp rw.cache-atblp))
  (%autoprove forcing-rw.cache-env-okp-of-rw.set-blockedp
              (%enable default rw.set-blockedp rw.cache-env-okp))
  (%autoprove forcing-rw.cache-lhses-okp-of-rw.set-blockedp
              (%enable default rw.set-blockedp rw.cache-lhses-okp)))


(defsection rw.cache-update
  (%autoadmit rw.cache-update)
  (%autoprove forcing-rw.cachep-of-rw.cache-update
              (%enable default rw.cache-update))
  (%autoprove forcing-rw.cache-assmsp-of-rw.cache-update
              (%enable default rw.cache-update rw.cache-assmsp))
  (%autoprove forcing-rw.cache-traces-okp-of-rw.cache-update
              (%enable default rw.cache-update rw.cache-traces-okp))
  (%autoprove forcing-rw.cache-atblp-of-rw.cache-update
              (%enable default rw.cache-update rw.cache-atblp))
  (%autoprove forcing-rw.cache-env-okp-of-rw.cache-update
              (%enable default rw.cache-update rw.cache-env-okp))
  (%autoprove forcing-rw.cache-lhses-okp-of-rw.cache-update
              (%enable default rw.cache-update rw.cache-lhses-okp)))


(defsection rw.cache-lookup
  (%autoadmit rw.cache-lookup)
  (%autoprove forcing-rw.tracep-of-rw.cache-lookup
              (%enable default rw.cache-lookup))
  (%autoprove forcing-rw.trace->iffp-of-rw.cache-lookup
              (%enable default rw.cache-lookup))
  (%autoprove forcing-rw.trace->hypbox-of-rw.cache-lookup
              (%enable default rw.cache-lookup rw.cache-assmsp))
  (%autoprove forcing-rw.trace->lhs-of-rw.cache-lookup
              (%enable default rw.cache-lookup rw.cache-lhses-okp))
  (%autoprove forcing-rw.trace-okp-of-rw.cache-lookup
              (%enable default rw.cache-lookup rw.cache-traces-okp))
  (%autoprove forcing-rw.trace-atblp-of-rw.cache-lookup
              (%enable default rw.cache-lookup rw.cache-atblp))
  (%autoprove forcing-rw.trace-env-okp-of-rw.cache-lookup
              (%enable default rw.cache-lookup rw.cache-env-okp)))


(defsection rw.empty-cache
  (%autoadmit rw.empty-cache)
  (%noexec rw.empty-cache)
  (%autoprove rw.cachep-of-rw.empty-cache
              (%enable default rw.empty-cache))
  (%autoprove rw.cache-assmsp-of-rw.empty-cache
              (%enable default rw.empty-cache rw.cache-assmsp))
  (%autoprove rw.cache-traces-okp-of-rw.empty-cache
              (%enable default rw.empty-cache rw.cache-traces-okp))
  (%autoprove rw.cache-atblp-of-rw.empty-cache
              (%enable default rw.empty-cache rw.cache-atblp))
  (%autoprove rw.cache-env-okp-of-rw.empty-cache
              (%enable default rw.empty-cache rw.cache-env-okp))
  (%autoprove rw.cache-lhses-okp-rw.empty-cache
              (%enable default rw.empty-cache rw.cache-lhses-okp)))


(defsection rw.maybe-update-cache
  (%autoadmit rw.maybe-update-cache)
  (%autoprove forcing-rw.cachep-of-rw.maybe-update-cache
              (%enable default rw.maybe-update-cache))
  (%autoprove forcing-rw.cache-assmsp-of-rw.maybe-update-cache
              (%enable default rw.maybe-update-cache))
  (%autoprove forcing-rw.cache-traces-okp-of-rw.maybe-update-cache
              (%enable default rw.maybe-update-cache))
  (%autoprove forcing-rw.cache-atblp-of-rw.maybe-update-cache
              (%enable default rw.maybe-update-cache))
  (%autoprove forcing-rw.cache-env-okp-of-rw.maybe-update-cache
              (%enable default rw.maybe-update-cache))
  (%autoprove forcing-rw.cache-lhses-okp-of-rw.maybe-update-cache
              (%enable default rw.maybe-update-cache)))


(%ensure-exactly-these-rules-are-missing "../../rewrite/cachep")

