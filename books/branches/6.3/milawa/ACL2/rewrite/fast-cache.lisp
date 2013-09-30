;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "cachep")
(include-book "fast-traces")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund rw.fast-cachelinep (x)
  (declare (xargs :guard t))
  (and (consp x)
       (let ((eqltrace (car x))
             (ifftrace (cdr x)))
         (and (implies eqltrace (rw.ftracep eqltrace))
              (implies ifftrace (rw.ftracep ifftrace))))))

(defund rw.fast-cacheline (eqltrace ifftrace)
  (declare (xargs :guard (and (or (not eqltrace)
                                  (rw.ftracep eqltrace))
                              (or (not ifftrace)
                                  (rw.ftracep ifftrace)))))
  (cons eqltrace ifftrace))

(defund rw.fast-cacheline->eqltrace (x)
  (declare (xargs :guard (rw.fast-cachelinep x)))
  (car x))

(defund rw.fast-cacheline->ifftrace (x)
  (declare (xargs :guard (rw.fast-cachelinep x)))
  (cdr x))

(defthm booleanp-of-rw.fast-cachelinep
  (equal (booleanp (rw.fast-cachelinep x))
         t)
  :hints(("Goal" :in-theory (enable rw.fast-cachelinep))))

(defthm forcing-rw.fast-cachelinep-of-rw.cacheline
  (implies (force (and (or (not eqltrace)
                           (rw.ftracep eqltrace))
                       (or (not ifftrace)
                           (rw.ftracep ifftrace))))
           (equal (rw.fast-cachelinep (rw.fast-cacheline eqltrace ifftrace))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-cachelinep rw.fast-cacheline))))

(defthm rw.fast-cacheline->eqltrace-of-rw.fast-cacheline
  (equal (rw.fast-cacheline->eqltrace (rw.fast-cacheline eqltrace ifftrace))
         eqltrace)
  :hints(("Goal" :in-theory (enable rw.fast-cacheline
                                    rw.fast-cacheline->eqltrace))))

(defthm rw.fast-cacheline->ifftrace-of-rw.cacheline
  (equal (rw.fast-cacheline->ifftrace (rw.fast-cacheline eqltrace ifftrace))
         ifftrace)
  :hints(("Goal" :in-theory (enable rw.fast-cacheline
                                    rw.fast-cacheline->ifftrace))))

(defthm forcing-rw.ftracep-of-rw.fast-cacheline->eqltrace
  (implies (force (rw.fast-cachelinep x))
           (equal (rw.ftracep (rw.fast-cacheline->eqltrace x))
                  (if (rw.fast-cacheline->eqltrace x)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable rw.fast-cacheline->eqltrace
                                    rw.fast-cachelinep))))

(defthm forcing-rw.ftracep-of-rw.fast-cacheline->ifftrace
  (implies (force (rw.fast-cachelinep x))
           (equal (rw.ftracep (rw.fast-cacheline->ifftrace x))
                  (if (rw.fast-cacheline->ifftrace x)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable rw.fast-cacheline->ifftrace rw.fast-cachelinep))))

(deflist rw.fast-cacheline-listp (x)
  (rw.fast-cachelinep x)
  :elementp-of-nil nil)




(defund rw.cacheline-fast-image (cacheline)
  (declare (xargs :guard (rw.cachelinep cacheline)))
  (let ((eqltrace (rw.cacheline->eqltrace cacheline))
        (ifftrace (rw.cacheline->ifftrace cacheline)))
    (rw.fast-cacheline (and eqltrace
                            (rw.trace-fast-image eqltrace))
                       (and ifftrace
                            (rw.trace-fast-image ifftrace)))))

(defthm rw.fast-cachelinep-of-rw.cacheline-fast-image
  (implies (force (rw.cachelinep cacheline))
           (equal (rw.fast-cachelinep (rw.cacheline-fast-image cacheline))
                  t))
  :hints(("Goal" :in-theory (enable rw.cacheline-fast-image))))


(defprojection :list (rw.cacheline-list-fast-image x)
               :element (rw.cacheline-fast-image x)
               :guard (rw.cacheline-listp x)
               :nil-preservingp nil)

(defthm rw.fast-cacheline-listp-of-rw.cacheline-list-fast-image
  (implies (force (rw.cacheline-listp x))
           (equal (rw.fast-cacheline-listp (rw.cacheline-list-fast-image x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))



(defmap :map (rw.fast-cachemapp x)
        :key (logic.termp x)
        :val (rw.fast-cachelinep x)
        :key-list (logic.term-listp x)
        :val-list (rw.fast-cacheline-listp x)
        :val-of-nil nil)

(defund rw.cachemap-fast-image (x)
  (declare (xargs :guard (rw.cachemapp x)))
  (if (consp x)
      (let ((key (car (car x)))
            (val (cdr (car x))))
        (cons (cons key (rw.cacheline-fast-image val))
              (rw.cachemap-fast-image (cdr x))))
    nil))

(defthm rw.fast-cachemapp-of-rw.cachemap-fast-image
  (implies (force (rw.cachemapp x))
           (equal (rw.fast-cachemapp (rw.cachemap-fast-image x))
                  t))
  :hints(("Goal" :in-theory (enable rw.cachemap-fast-image))))




(defaggregate rw.fast-cache
  (blockp data)
  :require ((booleanp-of-rw.fast-cache->blockp   (booleanp blockp))
            (rw.cachemapp-of-rw.fast-cache->data (rw.fast-cachemapp data)))
  :legiblep nil)

(defund rw.cache-fast-image (x)
  (declare (xargs :guard (rw.cachep x)))
  (rw.fast-cache (rw.cache->blockp x)
                 (rw.cachemap-fast-image (rw.cache->data x))))

(defthm rw.fast-cachep-of-rw.cache-fast-image
  (implies (force (rw.cachep x))
           (equal (rw.fast-cachep (rw.cache-fast-image x))
                  t))
  :hints(("Goal" :in-theory (enable rw.cache-fast-image))))

(defthm rw.fast-cache->blockp-of-rw.cache-fast-image
  (equal (rw.fast-cache->blockp (rw.cache-fast-image cache))
         (rw.cache->blockp cache))
  :hints(("Goal" :in-theory (enable rw.cache-fast-image))))

(defthm equal-of-rw.fast-cache-rewrite
  (implies (force (rw.fast-cachep cache))
           (equal (equal (rw.fast-cache blockp data) cache)
                  (and (equal (rw.fast-cache->blockp cache) blockp)
                       (equal (rw.fast-cache->data cache) data))))
  :hints(("Goal" :in-theory (enable rw.fast-cachep
                                    rw.fast-cache
                                    rw.fast-cache->blockp
                                    rw.fast-cache->data))))



(defund rw.fast-set-blockedp (blockedp cache)
  (declare (xargs :guard (and (booleanp blockedp)
                              (rw.fast-cachep cache))))
  (rw.fast-cache blockedp (rw.fast-cache->data cache)))

(defthm forcing-rw.fast-cachep-of-rw.set-blockedp
  (implies (force (and (booleanp blockedp)
                       (rw.fast-cachep cache)))
           (equal (rw.fast-cachep (rw.fast-set-blockedp blockedp cache))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-set-blockedp))))

(defthm rw.cache-fast-image-of-rw.set-blockedp
  (equal (rw.cache-fast-image (rw.set-blockedp blockedp x))
         (rw.fast-set-blockedp blockedp (rw.cache-fast-image x)))
  :hints(("Goal" :in-theory (enable rw.fast-set-blockedp
                                    rw.set-blockedp
                                    rw.cache-fast-image))))




(defund rw.fast-cache-update (term trace iffp cache)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.ftracep trace)
                              (rw.fast-cachep cache))))
  (let ((blockp (rw.fast-cache->blockp cache))
        (data   (rw.fast-cache->data cache)))
    (if (and blockp
             (not (logic.constantp (rw.ftrace->rhs trace))))
        cache
    (let* ((entry          (hons-lookup term data))
           (new-cache-line (if iffp
                               (rw.fast-cacheline (and entry (rw.fast-cacheline->eqltrace (cdr entry))) trace)
                             (rw.fast-cacheline trace (and entry (rw.fast-cacheline->ifftrace (cdr entry))))))
           (new-data       (hons-update term new-cache-line data)))
      (rw.fast-cache blockp new-data)))))

(defthm forcing-rw.fast-cachep-of-rw.cache-update
  (implies (force (and (logic.termp term)
                       (rw.ftracep trace)
                       (rw.fast-cachep cache)))
           (equal (rw.fast-cachep (rw.fast-cache-update term trace iffp cache))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-cache-update))))

(defthm cdr-of-lookup-of-term-in-rw.cachemap-fast-image
  (implies (force (rw.cachemapp x))
           (equal (cdr (lookup term (rw.cachemap-fast-image x)))
                  (if (lookup term (rw.cachemap-fast-image x))
                      (rw.cacheline-fast-image (cdr (lookup term x)))
                    nil)))
  :hints(("Goal" :in-theory (enable rw.cachemap-fast-image))))

(defthm lookup-of-term-in-rw.cachemap-fast-image
  (implies (force (rw.cachemapp x))
           (iff (lookup term (rw.cachemap-fast-image x))
                (lookup term x)))
  :hints(("Goal" :in-theory (enable rw.cachemap-fast-image))))

(defthm rw.cache-fast-image-of-rw.cache-update
  (implies (force (and (rw.cachep cache)
                       (logic.termp term)
                       (rw.tracep trace)))
           (equal (rw.cache-fast-image (rw.cache-update term trace iffp cache))
                  (rw.fast-cache-update term
                                        (rw.trace-fast-image trace)
                                        iffp
                                        (rw.cache-fast-image cache))))
  :hints(("Goal" :in-theory (enable rw.fast-cache-update
                                    rw.cache-update
                                    rw.cachemap-fast-image
                                    rw.cacheline-fast-image
                                    rw.cache-fast-image
                                    rw.trace-fast-image))))




(defund rw.maybe-update-fast-cache (condition term ftrace iffp fcache)
  (declare (xargs :guard (and (logic.termp term)
                              (rw.fast-cachep fcache)
                              (or (not condition)
                                  (rw.ftracep ftrace)))))
  (if condition
      (rw.fast-cache-update term ftrace iffp fcache)
    fcache))

(defthm forcing-rw.fast-cachep-of-rw.maybe-update-fast-cache
  (implies (force (and (logic.termp term)
                       (rw.ftracep trace)
                       (rw.fast-cachep cache)))
           (equal (rw.fast-cachep (rw.maybe-update-fast-cache condition term trace iffp cache))
                  t))
  :hints(("Goal" :in-theory (enable rw.maybe-update-fast-cache))))

(defthm rw.cache-fast-image-of-rw.maybe-update-cache
  (implies (force (AND (LOGIC.TERMP TERM)
                       (RW.CACHEP CACHE)
                       (OR (NOT CONDITION)
                           (AND (RW.TRACEP TRACE)
                                (EQUAL (RW.TRACE->IFFP TRACE) IFFP)
                                (EQUAL (RW.TRACE->LHS TRACE) TERM)))))
           (equal (rw.cache-fast-image (rw.maybe-update-cache condition term trace iffp cache))
                  (rw.maybe-update-fast-cache condition
                                              term
                                              (rw.trace-fast-image trace)
                                              iffp
                                              (rw.cache-fast-image cache))))
  :hints(("Goal" :in-theory (enable rw.maybe-update-fast-cache
                                    rw.maybe-update-cache))))






(defund rw.fast-cache-lookup (term iffp cache)
  (declare (xargs :guard (and (logic.termp term)
                              (booleanp iffp)
                              (rw.fast-cachep cache))))
  (let ((entry (hons-lookup term (rw.fast-cache->data cache))))
       (and entry
            (if iffp
                (rw.fast-cacheline->ifftrace (cdr entry))
              (rw.fast-cacheline->eqltrace (cdr entry))))))

(defthm forcing-rw.ftracep-of-rw.fast-cache-lookup
  (implies (force (rw.fast-cachep cache))
           (equal (rw.ftracep (rw.fast-cache-lookup term iffp cache))
                  (if (rw.fast-cache-lookup term iffp cache)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable rw.fast-cache-lookup))))

(defthm rw.fast-cache-lookup-of-rw.cache-fast-image
  (implies (force (and (logic.termp term)
                       (booleanp iffp)
                       (rw.cachep cache)))
           (equal (rw.fast-cache-lookup term iffp (rw.cache-fast-image cache))
                  (if (rw.cache-lookup term iffp cache)
                      (rw.trace-fast-image (rw.cache-lookup term iffp cache))
                    nil)))
  :hints(("Goal" :in-theory (enable rw.fast-cache-lookup
                                    rw.cache-lookup
                                    rw.cache-fast-image
                                    rw.cacheline-fast-image
                                    rw.cachemap-fast-image))))



(defund rw.fast-empty-cache ()
  (declare (xargs :guard t))
  (rw.fast-cache nil nil))

(in-theory (disable (:executable-counterpart rw.fast-empty-cache)))

(defthm rw.fast-cachep-of-rw.fast-empty-cache
  (equal (rw.fast-cachep (rw.fast-empty-cache))
         t)
  :hints(("Goal" :in-theory (enable rw.fast-empty-cache))))

(defthm rw.cache-fast-image-of-rw.empty-cache
  (equal (rw.cache-fast-image (rw.empty-cache))
         (rw.fast-empty-cache))
  :hints(("Goal" :in-theory (enable rw.empty-cache rw.fast-empty-cache))))






(defconst *rw.fast-cache-sigma*
  ;; Substitutions to switch over to a fast cache.
  (list (cons '(rw.empty-cache)
              '(rw.fast-empty-cache))
        (cons '(rw.cache-lookup ?term ?iffp ?cache)
              '(rw.fast-cache-lookup ?term ?iffp ?cache))
        (cons '(rw.cache-update ?term ?trace ?iffp ?cache)
              '(rw.fast-cache-update ?term ?trace ?iffp ?cache))
        (cons '(rw.maybe-update-cache ?condition ?term ?trace ?iffp ?cache)
              '(rw.maybe-update-fast-cache ?condition ?term ?trace ?iffp ?cache))
        (cons '(rw.set-blockedp ?blockedp ?cache)
              '(rw.fast-set-blockedp ?blockedp ?cache))
        (cons '(rw.cache->blockp ?cache)
              '(rw.fast-cache->blockp ?cache))))

