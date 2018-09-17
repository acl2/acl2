; Copyright (C) 2017, Regents of the University of Texas
; Written by Mihir Mehta
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

;  fat32.lisp                                  Mihir Mehta

; Utilities for FAT32.

; The following is in fat32.acl2, but we include it here as well for
; when we are doing interactive development, in order to read gl:: symbols.
(include-book "centaur/gl/portcullis" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "file-system-lemmas")
(include-book "bounded-nat-listp")

(defconst *expt-2-28* (expt 2 28))

;; from page 18 of the FAT specification
(defconst *ms-end-of-clusterchain* (- *expt-2-28* 1))

;; from page 14 of the FAT specification
(defconst *ms-first-data-cluster* 2)

;; from page 18 of the FAT specification
(defconst *ms-bad-cluster* 268435447)

;; from page 15 of the FAT specification
(defconst *ms-fat32-min-count-of-clusters* 65525)

;; from page 9 of the FAT specification
(defconst *ms-min-bytes-per-sector* 512)

;; inferred - there can be as few as one sectors in a cluster
(defconst *ms-min-data-region-size* (* *ms-min-bytes-per-sector*
                                       1
                                       *ms-fat32-min-count-of-clusters*))

(defconst *ms-max-bytes-per-sector* 4096)

;; inferred - there can be as many as 128 sectors in a cluster
(defconst *ms-max-data-region-size* (* *ms-max-bytes-per-sector*
                                       128
                                       (- *ms-bad-cluster* 2)))

(defconst *ms-dir-ent-length* 32)

;; from include/uapi/asm-generic/errno-base.h
(defconst *ENOENT* 2) ;; No such file or directory
(defconst *EIO* 5) ;; I/O error
(defconst *EBADF* 9) ;; Bad file number
(defconst *EEXIST* 17) ;; File exists
(defconst *ENOTDIR* 20)	;; Not a directory
(defconst *EISDIR* 21) ;; Is a directory
(defconst *ENOSPC* 28) ;; No space left on device
(defconst *ENAMETOOLONG* 36) ;; File name too long

(defund fat32-entry-p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 32 x))

(defund fat32-masked-entry-p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 28 x))

;; 0 is chosen as the default value based on this comment from Microsoft's FAT
;; overview:
;; The only time that the high 4 bits of FAT32 FAT entries should ever be
;; changed is when the volume is formatted, at which time the whole 32-bit FAT
;; entry should be zeroed, including the high 4 bits.
(defund fat32-entry-fix (x)
  (declare (xargs :guard t))
  (if (fat32-entry-p x)
      x 0))

(defund fat32-masked-entry-fix (x)
  (declare (xargs :guard t))
  (if (fat32-masked-entry-p x)
      x 0))

(in-theory (enable fat32-entry-p fat32-entry-fix fat32-masked-entry-p fat32-masked-entry-fix))

(defthm fat32-masked-entry-p-correctness-1
  (implies (fat32-masked-entry-p x)
           (natp x))
  :rule-classes :forward-chaining)

;; Use a mask to take the low 28 bits.
(defund fat32-entry-mask (x)
  (declare (xargs :guard (fat32-entry-p x)))
  (logand x (- (ash 1 28) 1)))

(defthm
  fat32-entry-mask-correctness-1
  (fat32-masked-entry-p (fat32-entry-mask x))
  :hints (("goal" :in-theory (e/d (fat32-entry-mask fat32-masked-entry-p)
                                  (unsigned-byte-p logand-ash-lemma-1))
           :use (:instance logand-ash-lemma-1 (c 28)
                           (i x)))))

(fty::deffixtype fat32-entry
                 :pred   fat32-entry-p
                 :fix    fat32-entry-fix
                 :equiv  fat32-entry-equiv
                 :define t
                 :forward t
                 )

(fty::deffixtype fat32-masked-entry
                 :pred   fat32-masked-entry-p
                 :fix    fat32-masked-entry-fix
                 :equiv  fat32-masked-entry-equiv
                 :define t
                 :forward t
                 )

(fty::deflist fat32-entry-list :elt-type fat32-entry-p :true-listp t)

(fty::deflist fat32-masked-entry-list :elt-type fat32-masked-entry-p :true-listp t)

(defthm nat-listp-if-fat32-masked-entry-list-p
  (implies (fat32-masked-entry-list-p x)
           (nat-listp x))
  :rule-classes (:forward-chaining :rewrite))

(in-theory (disable fat32-entry-p fat32-entry-fix fat32-masked-entry-p fat32-masked-entry-fix))

(defthm member-of-fat32-entry-list
  (implies (and (member-equal x lst)
                (fat32-entry-list-p lst))
           (fat32-entry-p x)))

(defthm
  fat32-masked-entry-list-p-of-make-list-ac
  (implies (and (fat32-masked-entry-p val)
                (fat32-masked-entry-list-p ac))
           (fat32-masked-entry-list-p (make-list-ac n val ac))))

(defthm fat32-masked-entry-list-p-of-append
  (implies (true-listp x)
           (equal (fat32-masked-entry-list-p (binary-append x y))
                  (and (fat32-masked-entry-list-p x)
                       (fat32-masked-entry-list-p y)))))

(defthm fat32-entry-list-p-of-update-nth
  (implies (and (< key (len l))
                (fat32-entry-list-p l))
           (equal (fat32-entry-list-p (update-nth key val l))
                  (fat32-entry-p val))))

(defthm set-indices-in-fa-table-guard-lemma-2
  (implies (fat32-entry-p x) (natp x))
  :hints (("goal" :in-theory (enable fat32-entry-p)))
  :rule-classes :forward-chaining)

(defthm fat32-entry-p-of-nth
  (implies (and (fat32-entry-list-p l)
                (< (nfix n) (len l)))
           (fat32-entry-p (nth n l))))

(defund
  fat32-update-lower-28
  (entry masked-entry)
  (declare
   (xargs
    :guard-hints
    (("goal"
      :in-theory (enable fat32-entry-p fat32-masked-entry-p)))
    :guard (and (fat32-entry-p entry)
                (fat32-masked-entry-p masked-entry))))
  (logior (logand entry (- (ash 1 32) (ash 1 28)))
          masked-entry))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (defthm
    fat32-update-lower-28-correctness-1
    (implies
     (and (fat32-entry-p entry)
          (fat32-masked-entry-p masked-entry))
     (fat32-entry-p (fat32-update-lower-28 entry masked-entry)))
    :hints
    (("goal"
      :in-theory (e/d nil (unsigned-byte-p logand logior)
                      (fat32-entry-p fat32-masked-entry-p
                                     fat32-update-lower-28)))
     ("goal''" :in-theory (enable unsigned-byte-p)))))

; :Redef helps here for overcoming lemmas that are incompatible here (and
; finding all such lemmas in the process).
(encapsulate
  ()

  (local
   (include-book "centaur/gl/gl" :dir :system))

  (local
   (def-gl-thm fat32-update-lower-28-correctness-2
     :hyp (and (fat32-entry-p entry)
               (fat32-masked-entry-p masked-entry))
     :concl (equal (fat32-entry-mask (fat32-update-lower-28 entry
                                                            masked-entry))
                   masked-entry)
     :g-bindings (gl::auto-bindings (:nat entry 33) (:nat masked-entry 29))))

  (defthm
    fat32-update-lower-28-correctness-2
    (implies
     (and (fat32-entry-p entry)
          (fat32-masked-entry-p masked-entry))
     (equal
      (fat32-entry-mask (fat32-update-lower-28 entry masked-entry)) masked-entry))))

;; taken from page 18 of the fat overview - the constant 268435448 is written
;; out as 0xFFFFFF8 therein
(defund fat32-is-eof (fat-content)
  (declare (xargs :guard (fat32-masked-entry-p fat-content)
                  :guard-hints (("Goal'" :in-theory (enable fat32-masked-entry-p)))))
  (>= fat-content 268435448))

(defthm fat32-is-eof-correctness-1
  (implies (< fat-content *ms-bad-cluster*)
           (not (fat32-is-eof fat-content)))
  :hints (("Goal" :in-theory (enable fat32-is-eof)) ))

(defun
    fat32-build-index-list
    (fa-table masked-current-cluster length cluster-size)
  (declare
   (xargs
    :measure (nfix length)
    :guard (and (fat32-entry-list-p fa-table)
                (fat32-masked-entry-p masked-current-cluster)
                (natp length)
                (>= masked-current-cluster 2)
                (< masked-current-cluster (len fa-table))
                (integerp cluster-size)
                (> cluster-size 0))))
  (if
      (or (zp length) (zp cluster-size))
      ;; This represents a problem case because masked-current-cluster is a
      ;; valid non-free cluster, but the length is 0. This loosely corresponds
      ;; to the infinite loop protection in the function
      ;; fs/fat/cache.c:fat_get_cluster
      (mv nil (- *eio*))
    (let
        ((masked-next-cluster
          (fat32-entry-mask (nth masked-current-cluster fa-table))))
      (if
          (< masked-next-cluster 2)
          (mv (list masked-current-cluster)
              (- *eio*))
        (if
            (or (fat32-is-eof masked-next-cluster)
                (>= masked-next-cluster (len fa-table)))
            (mv (list masked-current-cluster) 0)
          (b*
              (((mv tail-index-list tail-error)
                (fat32-build-index-list fa-table masked-next-cluster
                                        (nfix (- length cluster-size))
                                        cluster-size)))
            (mv (list* masked-current-cluster tail-index-list)
                tail-error)))))))

(defthm fat32-build-index-list-correctness-1
  (implies (and (equal b (len fa-table))
                (fat32-masked-entry-p masked-current-cluster)
                (< masked-current-cluster (len fa-table)))
           (b* (((mv index-list &)
                 (fat32-build-index-list fa-table masked-current-cluster
                                         length cluster-size)))
             (bounded-nat-listp index-list b))))

(defthm
  fat32-build-index-list-correctness-2
  (implies
   (and
    (fat32-masked-entry-p masked-current-cluster)
    (>= masked-current-cluster *ms-first-data-cluster*)
    (< masked-current-cluster (len fa-table)))
   (b* (((mv index-list &)
         (fat32-build-index-list fa-table masked-current-cluster
                                 length cluster-size)))
     (fat32-masked-entry-list-p index-list))))

(defthm
  fat32-build-index-list-correctness-3
  (b* (((mv & error-code)
        (fat32-build-index-list fa-table masked-current-cluster
                                length cluster-size)))
    (and (integerp error-code)
         (or (equal error-code 0)
             (equal error-code (- *eio*))))))

(defthm
  fat32-build-index-list-correctness-4
  (implies
   (fat32-masked-entry-p masked-current-cluster)
   (mv-let
     (index-list error-code)
     (fat32-build-index-list fa-table masked-current-cluster
                             length cluster-size)
     (implies
      (and (fat32-masked-entry-p key)
           (< key (len fa-table))
           (not (member-equal key index-list))
           (equal error-code 0))
      (equal
       (fat32-build-index-list (update-nth key val fa-table)
                               masked-current-cluster
                               length cluster-size)
       (fat32-build-index-list fa-table masked-current-cluster
                               length cluster-size)))))
  :hints
  (("subgoal *1/3"
    :expand
    (fat32-build-index-list (update-nth key val fa-table)
                            masked-current-cluster
                            length cluster-size))))

(defthm
  fat32-build-index-list-correctness-5
  (implies
   (and (fat32-masked-entry-p masked-current-cluster)
        (<= *ms-first-data-cluster*
            masked-current-cluster))
   (lower-bounded-integer-listp
    (mv-nth
     0
     (fat32-build-index-list fa-table masked-current-cluster
                             length cluster-size))
    *ms-first-data-cluster*))
  :hints
  (("goal" :in-theory (enable lower-bounded-integer-listp))))

(defund
  find-n-free-clusters-helper
  (fa-table n start)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (natp n)
                              (natp start))))
  (if (or (atom fa-table) (zp n))
      nil
      (if (not (equal (fat32-entry-mask (car fa-table))
                      0))
          (find-n-free-clusters-helper (cdr fa-table)
                                       n (+ start 1))
          (cons start
                (find-n-free-clusters-helper (cdr fa-table)
                                             (- n 1)
                                             (+ start 1))))))

(defthmd
  find-n-free-clusters-helper-correctness-1
  (implies (and (fat32-entry-list-p fa-table)
                (natp n)
                (natp start)
                (equal b (+ start (len fa-table))))
           (bounded-nat-listp
            (find-n-free-clusters-helper fa-table n start)
            b))
  :hints
  (("goal'" :in-theory (enable find-n-free-clusters-helper))))

(defthmd
  find-n-free-clusters-helper-correctness-2
  (implies
   (natp start)
   (nat-listp (find-n-free-clusters-helper fa-table n start)))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters-helper))))

(defthmd
  find-n-free-clusters-helper-correctness-3
  (implies
   (and
    (natp start)
    (member-equal x (find-n-free-clusters-helper fa-table n start)))
   (and (integerp x) (<= start x)))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters-helper))))

(defthm
  find-n-free-clusters-helper-correctness-4
  (implies
   (and (fat32-entry-list-p fa-table)
        (natp n)
        (natp start)
        (member-equal
         x
         (find-n-free-clusters-helper fa-table n start)))
   (equal (fat32-entry-mask (nth (- x start) fa-table))
          0))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters-helper)
    :use find-n-free-clusters-helper-correctness-3)
   ("subgoal *1/2"
    :use (:instance find-n-free-clusters-helper-correctness-3
                    (fa-table (cdr fa-table))
                    (start (+ 1 start))))))

(defthm find-n-free-clusters-guard-lemma-1
  (implies (fat32-entry-list-p l)
           (fat32-entry-list-p (nthcdr n l))))

(defund
    find-n-free-clusters (fa-table n)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (natp n))))
  ;; the first 2 clusters are excluded
  (find-n-free-clusters-helper
   (nthcdr *ms-first-data-cluster* fa-table)
   n *ms-first-data-cluster*))

(defthm
  find-n-free-clusters-correctness-1
  (implies (and (fat32-entry-list-p fa-table)
                (natp n)
                (equal b (len fa-table))
                (>= (len fa-table)
                    *ms-first-data-cluster*))
           (bounded-nat-listp (find-n-free-clusters fa-table n)
                              b))
  :hints
  (("goal"
    :in-theory (enable find-n-free-clusters)
    :use
    ((:instance
      find-n-free-clusters-helper-correctness-1
      (start *ms-first-data-cluster*)
      (fa-table (nthcdr *ms-first-data-cluster* fa-table))
      (b (len fa-table))))))
  :rule-classes
  (:rewrite
   (:linear
    :corollary
    (implies (and (fat32-entry-list-p fa-table)
                  (natp n)
                  (equal b (len fa-table))
                  (>= (len fa-table)
                      *ms-first-data-cluster*)
                  (consp (find-n-free-clusters fa-table n)))
             (< (car (find-n-free-clusters fa-table n))
                b)))))

(defthm
  find-n-free-clusters-correctness-2
  (nat-listp (find-n-free-clusters fa-table n))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (consp (find-n-free-clusters fa-table n))
             (and (nat-listp (cdr (find-n-free-clusters fa-table n)))
                  (integerp (car (find-n-free-clusters fa-table n))))))
   (:linear
    :corollary (implies (consp (find-n-free-clusters fa-table n))
                        (<= 0
                            (car (find-n-free-clusters fa-table n))))))
  :hints
  (("goal"
    :in-theory (enable find-n-free-clusters
                       find-n-free-clusters-helper-correctness-2))))

(defthmd
  find-n-free-clusters-correctness-3
  (implies (member-equal x (find-n-free-clusters fa-table n))
           (and (integerp x) (<= *ms-first-data-cluster* x)))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters))
   ("goal'"
    :use (:instance find-n-free-clusters-helper-correctness-3
                    (start *ms-first-data-cluster*)
                    (fa-table (nthcdr *ms-first-data-cluster* fa-table))))))

(defthmd
  find-n-free-clusters-correctness-4
  (implies
   (and (fat32-entry-list-p fa-table)
        (natp n)
        (natp start)
        (member-equal x (find-n-free-clusters fa-table n)))
   (equal (fat32-entry-mask (nth x fa-table))
          0))
  :hints
  (("goal"
    :in-theory (enable find-n-free-clusters)
    :use
    (:instance
     find-n-free-clusters-helper-correctness-4
     (start *ms-first-data-cluster*)
     (fa-table (nthcdr *ms-first-data-cluster* fa-table))))
   ("goal''"
    :in-theory (disable member-of-a-nat-list)
    :use
    ((:instance
      member-of-a-nat-list
      (lst (find-n-free-clusters-helper
            (nthcdr *ms-first-data-cluster* fa-table)
            n *ms-first-data-cluster*)))))
   ("subgoal 2"
    :use
    (:instance
     find-n-free-clusters-helper-correctness-3
     (fa-table (nthcdr *ms-first-data-cluster* fa-table))
     (start *ms-first-data-cluster*)))))

(defthmd
  fat32-masked-entry-list-p-alt
  (equal (fat32-masked-entry-list-p x)
         (bounded-nat-listp x *expt-2-28*))
  :hints (("goal" :in-theory (enable fat32-masked-entry-p))))

(defthm
  fat32-masked-entry-list-p-of-find-n-free-clusters
  (implies (and (fat32-entry-list-p fa-table)
                (natp n)
                (>= (len fa-table) *ms-first-data-cluster*)
                (<= (len fa-table) *ms-bad-cluster*))
           (fat32-masked-entry-list-p (find-n-free-clusters fa-table n)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (fat32-entry-list-p fa-table)
          (natp n)
          (>= (len fa-table) *ms-first-data-cluster*)
          (<= (len fa-table) *ms-bad-cluster*))
     (let ((l (find-n-free-clusters fa-table n)))
       (implies (consp l)
                (and (fat32-masked-entry-list-p (cdr l))
                     (fat32-masked-entry-p (car l))))))))
  :hints (("goal" :in-theory (disable find-n-free-clusters-correctness-1)
           :use ((:instance find-n-free-clusters-correctness-1
                            (b (len fa-table)))
                 (:instance fat32-masked-entry-list-p-alt
                            (x (find-n-free-clusters fa-table n)))
                 (:instance bounded-nat-listp-correctness-5
                            (l (find-n-free-clusters fa-table n))
                            (x (len fa-table))
                            (y *expt-2-28*))))))

(defthm
  lower-bounded-integer-listp-of-find-n-free-clusters-helper
  (implies (integerp start)
           (lower-bounded-integer-listp
            (find-n-free-clusters-helper fa-table n start)
            start))
  :hints
  (("goal" :in-theory (enable lower-bounded-integer-listp
                              find-n-free-clusters-helper))
   ("subgoal *1/5.1'"
    :use
    (:instance lower-bounded-integer-listp-correctness-5
               (l (find-n-free-clusters-helper (cdr fa-table)
                                               (+ -1 n)
                                               (+ 1 start)))
               (x (+ 1 start))
               (y start)))
   ("subgoal *1/3''"
    :use
    (:instance lower-bounded-integer-listp-correctness-5
               (l (find-n-free-clusters-helper (cdr fa-table)
                                               n (+ 1 start)))
               (x (+ 1 start))
               (y start)))))

(defthm
  lower-bounded-integer-listp-of-find-n-free-clusters
  (lower-bounded-integer-listp (find-n-free-clusters fa-table n)
                               *ms-first-data-cluster*)
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (consp (find-n-free-clusters fa-table n))
     (lower-bounded-integer-listp (cdr (find-n-free-clusters fa-table n))
                                  *ms-first-data-cluster*))
    :hints (("goal" :in-theory (enable lower-bounded-integer-listp))))
   (:linear
    :corollary (implies (consp (find-n-free-clusters fa-table n))
                        (<= *ms-first-data-cluster*
                            (car (find-n-free-clusters fa-table n))))
    :hints (("goal" :in-theory (enable lower-bounded-integer-listp)))))
  :hints (("goal" :in-theory (enable find-n-free-clusters))))

(defund
  set-indices-in-fa-table
  (fa-table index-list value-list)
  (declare
   (xargs :measure (acl2-count index-list)
          :guard (and (fat32-entry-list-p fa-table)
                      (nat-listp index-list)
                      (fat32-masked-entry-list-p value-list)
                      (equal (len index-list)
                             (len value-list)))))
  (if
   (atom index-list)
   fa-table
   (let
    ((current-index (car index-list)))
    (if
     (or (not (natp current-index))
         (>= current-index (len fa-table)))
     fa-table
     (set-indices-in-fa-table
      (update-nth current-index
                  (fat32-update-lower-28 (nth current-index fa-table)
                                         (car value-list))
                  fa-table)
      (cdr index-list)
      (cdr value-list))))))

(defthm
  set-indices-in-fa-table-correctness-1
  (implies
   (and (fat32-entry-list-p fa-table)
        (bounded-nat-listp index-list (len fa-table))
        (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list)))
   (fat32-entry-list-p
    (set-indices-in-fa-table fa-table index-list value-list)))
  :hints (("Goal" :in-theory (enable set-indices-in-fa-table))))

(defthm
  set-indices-in-fa-table-correctness-2
  (equal (len (set-indices-in-fa-table fa-table index-list value-list))
         (len fa-table))
  :hints (("goal" :in-theory (enable set-indices-in-fa-table))))

;; Well, it might not be a great idea to borrow a numbering scheme from
;; set-indices.lisp
(defthm set-indices-in-fa-table-correctness-3
  (implies (and (natp n)
                (nat-listp index-list)
                (not (member-equal n index-list)))
           (equal (nth n (set-indices-in-fa-table fa-table index-list value-list))
                  (nth n fa-table)))
  :hints (("Goal" :in-theory (enable set-indices-in-fa-table))))

(defthm set-indices-in-fa-table-correctness-4
  (implies (and (natp key)
                (< key (len l))
                (nat-listp index-list)
                (not (member-equal key index-list)))
           (equal (set-indices-in-fa-table (update-nth key val l) index-list value-list)
                  (update-nth key val (set-indices-in-fa-table l index-list value-list))))
  :hints (("Goal" :in-theory (enable set-indices-in-fa-table))))
