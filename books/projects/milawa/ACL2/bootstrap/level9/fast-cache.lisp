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
(include-book "cachep")
(include-book "fast-traces")
(%interactive)



(%autoadmit rw.fast-cachelinep)
(%autoadmit rw.fast-cacheline)
(%autoadmit rw.fast-cacheline->eqltrace)
(%autoadmit rw.fast-cacheline->ifftrace)

(%autoprove booleanp-of-rw.fast-cachelinep
            (%enable default rw.fast-cachelinep))

(%autoprove forcing-rw.fast-cachelinep-of-rw.cacheline
            (%enable default rw.fast-cachelinep rw.fast-cacheline))

(%autoprove rw.fast-cacheline->eqltrace-of-rw.fast-cacheline
            (%enable default rw.fast-cacheline rw.fast-cacheline->eqltrace))

(%autoprove rw.fast-cacheline->ifftrace-of-rw.cacheline
            (%enable default rw.fast-cacheline rw.fast-cacheline->ifftrace))

(%autoprove forcing-rw.ftracep-of-rw.fast-cacheline->eqltrace
            (%enable default rw.fast-cacheline->eqltrace rw.fast-cachelinep))

(%autoprove forcing-rw.ftracep-of-rw.fast-cacheline->ifftrace
            (%enable default rw.fast-cacheline->ifftrace rw.fast-cachelinep))

(%deflist rw.fast-cacheline-listp (x)
          (rw.fast-cachelinep x))



(%autoadmit rw.cacheline-fast-image)

(%autoprove rw.fast-cachelinep-of-rw.cacheline-fast-image
            (%enable default rw.cacheline-fast-image))


(%defprojection :list (rw.cacheline-list-fast-image x)
                :element (rw.cacheline-fast-image x))

(%autoprove rw.fast-cacheline-listp-of-rw.cacheline-list-fast-image
            (%cdr-induction x))



(%defmap :map (rw.fast-cachemapp x)
         :key (logic.termp x)
         :val (rw.fast-cachelinep x)
         :key-list (logic.term-listp x)
         :val-list (rw.fast-cacheline-listp x)
         :val-of-nil nil)



(%autoadmit rw.cachemap-fast-image)

(%autoprove rw.fast-cachemapp-of-rw.cachemap-fast-image
            (%cdr-induction x)
            (%restrict default rw.cachemap-fast-image (equal x 'x)))



(%defaggregate rw.fast-cache
  (blockp data)
  :require ((booleanp-of-rw.fast-cache->blockp   (booleanp blockp))
            (rw.cachemapp-of-rw.fast-cache->data (rw.fast-cachemapp data))))

(%autoadmit rw.cache-fast-image)

(%autoprove rw.fast-cachep-of-rw.cache-fast-image
            (%enable default rw.cache-fast-image))

(%autoprove rw.fast-cache->blockp-of-rw.cache-fast-image
            (%enable default rw.cache-fast-image))

(%autoprove equal-of-rw.fast-cache-rewrite
            (%enable default
                     rw.fast-cachep
                     rw.fast-cache
                     rw.fast-cache->blockp
                     rw.fast-cache->data))

(defthm equal-of-rw.fast-cache-rewrite-alt
  (implies (force (rw.fast-cachep cache))
           (equal (equal cache (rw.fast-cache blockp data))
                  (and (equal (rw.fast-cache->blockp cache) blockp)
                       (equal (rw.fast-cache->data cache) data)))))

(%autoprove equal-of-rw.fast-cache-rewrite-alt
            (%use (%thm equal-of-rw.fast-cache-rewrite)))



(%autoadmit rw.fast-set-blockedp)

(%autoprove forcing-rw.fast-cachep-of-rw.set-blockedp
            (%enable default rw.fast-set-blockedp))

(%autoprove rw.cache-fast-image-of-rw.set-blockedp
            (%enable default
                     rw.fast-set-blockedp
                     rw.set-blockedp
                     rw.cache-fast-image))



(%autoadmit rw.fast-cache-update)

(%autoprove forcing-rw.fast-cachep-of-rw.cache-update
            (%enable default rw.fast-cache-update))

(%autoprove cdr-of-lookup-of-term-in-rw.cachemap-fast-image
            (%cdr-induction x)
            (%restrict default rw.cachemap-fast-image (equal x 'x)))

(%autoprove lookup-of-term-in-rw.cachemap-fast-image
            (%cdr-induction x)
            (%restrict default rw.cachemap-fast-image (equal x 'x)))

(%autoprove rw.cache-fast-image-of-rw.cache-update
            (%enable default rw.fast-cache-update rw.cache-update)
            (%enable default rw.cache-fast-image rw.trace-fast-image)
            (%restrict default rw.cachemap-fast-image (and (consp x) (equal (car x) 'cons)))
            (%enable default rw.cacheline-fast-image))




(%autoadmit rw.maybe-update-fast-cache)

(%autoprove forcing-rw.fast-cachep-of-rw.maybe-update-fast-cache
            (%enable default rw.maybe-update-fast-cache))

(%autoprove rw.cache-fast-image-of-rw.maybe-update-cache
            (%enable default rw.maybe-update-fast-cache rw.maybe-update-cache))




(%autoadmit rw.fast-cache-lookup)

(%autoprove forcing-rw.ftracep-of-rw.fast-cache-lookup
            (%enable default rw.fast-cache-lookup))

(%autoprove rw.fast-cache-lookup-of-rw.cache-fast-image
            (%enable default rw.fast-cache-lookup rw.cache-lookup rw.cache-fast-image rw.cacheline-fast-image)
            (%restrict default rw.cachemap-fast-image (and (consp x) (equal (car x) 'cons))))



(%autoadmit rw.fast-empty-cache)
(%noexec rw.fast-empty-cache)

(%autoprove rw.fast-cachep-of-rw.fast-empty-cache
            (%enable default rw.fast-empty-cache))

(%autoprove rw.cache-fast-image-of-rw.empty-cache
            (%enable default rw.empty-cache rw.fast-empty-cache))



