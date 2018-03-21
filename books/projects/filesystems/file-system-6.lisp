; Copyright (C) 2017, Regents of the University of Texas
; Written by Mihir Mehta
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

;  file-system-6.lisp                                  Mihir Mehta

; Here we build on model 4 to add a file allocation table. We follow exactly
; the allocation strategy laid out in model 4. To allow this to happen, we must
; set our cluster size to 1 sector, and our sector size to 8 bytes. This is
; based on every character in ACL2 being a byte.

; The following is in file-system-6.acl2, but we include it here as well for
; when we are doing interactive development, in order to read gl:: symbols.
(include-book "centaur/gl/portcullis" :dir :system)

(include-book "file-system-4")
(include-book "centaur/fty/top" :dir :system)

(defconst *expt-2-28* (expt 2 28))
;; from page 18 of the FAT specification
(defconst *MS-END-OF-CLUSTERCHAIN* (- *expt-2-28* 1))
;; from page 14 of the FAT specification
(defconst *ms-first-data-cluster* 2)
;; from page 18 of the FAT specification
(defconst *ms-bad-cluster* 268435447)

;; from include/uapi/asm-generic/errno-base.h
(defconst *EIO* 5) ;; I/O error
(defconst *ENOSPC* 28) ;; No space left on device
(defconst *ENOENT* 2) ;; No such file or directory

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

(defthm set-indices-in-fa-table-guard-lemma-1
  (implies (and (natp key)
                (< key (len l))
                (fat32-entry-list-p l)
                (fat32-entry-p val))
           (fat32-entry-list-p (update-nth key val l))))

(defthm set-indices-in-fa-table-guard-lemma-2
  (implies (fat32-entry-p x) (natp x))
  :hints (("goal" :in-theory (enable fat32-entry-p)))
  :rule-classes :forward-chaining)

(defthm set-indices-in-fa-table-guard-lemma-3
  (implies (and (fat32-entry-list-p l)
                (natp n)
                (< n (len l)))
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

;; question: if fat entries are 28 bits long, then how is the maximum size
;; determined to be 4 GB?
;; also, how are we gonna do this without a feasible length restriction?
(defund l6-regular-file-entry-p (entry)
  (declare (xargs :guard t))
  (and (consp entry)
       ;; fat entries are effectively 28 bits long
       (fat32-masked-entry-p (car entry))
       (natp (cdr entry))))

(defund l6-regular-file-first-cluster (entry)
  (declare (xargs :guard (l6-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l6-regular-file-entry-p)))))
  (car entry))

(defund l6-regular-file-length (entry)
  (declare (xargs :guard (l6-regular-file-entry-p entry)
                  :guard-hints (("Goal" :in-theory (enable l6-regular-file-entry-p)))))
  (cdr entry))

(defthm
  l6-regular-file-entry-p-correctness-1
  (implies
   (l6-regular-file-entry-p entry)
   (and
    (fat32-masked-entry-p (l6-regular-file-first-cluster entry))
    (integerp (l6-regular-file-first-cluster entry))
    (>= (l6-regular-file-first-cluster entry)
        0)
    (< (l6-regular-file-first-cluster entry)
       *expt-2-28*)
    (integerp (l6-regular-file-length entry))
    (>= (l6-regular-file-length entry) 0)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (l6-regular-file-entry-p entry)
     (and (fat32-masked-entry-p
           (l6-regular-file-first-cluster entry))
          (integerp (l6-regular-file-first-cluster entry))
          (integerp (l6-regular-file-length entry)))))
   (:linear
    :corollary
    (implies (l6-regular-file-entry-p entry)
             (and (>= (l6-regular-file-first-cluster entry)
                      0)
                  (< (l6-regular-file-first-cluster entry)
                     *expt-2-28*)
                  (>= (l6-regular-file-length entry)
                      0)))))
  :hints
  (("goal" :in-theory (enable l6-regular-file-entry-p
                              l6-regular-file-first-cluster
                              l6-regular-file-length
                              fat32-masked-entry-p))))

(defund
  l6-make-regular-file
  (first-cluster length)
  (declare
   (xargs :guard (and (fat32-masked-entry-p first-cluster)
                      (natp length))))
  (cons first-cluster length))

(defthm
  l6-make-regular-file-correctness-1
  (implies (and (fat32-masked-entry-p first-cluster)
                (natp length))
           (l6-regular-file-entry-p
            (l6-make-regular-file first-cluster length)))
  :hints (("goal" :in-theory (enable l6-regular-file-entry-p
                                     l6-make-regular-file))))

(defthm
  l6-make-regular-file-correctness-2
  (let ((entry (l6-make-regular-file first-cluster length)))
       (and (equal (l6-regular-file-first-cluster entry)
                   first-cluster)
            (equal (l6-regular-file-length entry)
                   length)))
  :hints
  (("goal" :in-theory (enable l6-make-regular-file
                              l6-regular-file-first-cluster
                              l6-regular-file-length))))

; This function defines a valid filesystem. It's an alist where all the cars
; are symbols and all the cdrs are either further filesystems or regular files.
(defun l6-fs-p (fs)
  (declare (xargs :guard t))
  (if (atom fs)
      (null fs)
    (and (let ((directory-or-file-entry (car fs)))
           (if (atom directory-or-file-entry)
               nil
             (let ((name (car directory-or-file-entry))
                   (entry (cdr directory-or-file-entry)))
               (and (symbolp name)
                    (or (l6-regular-file-entry-p entry)
                        (l6-fs-p entry))))))
         (l6-fs-p (cdr fs)))))

(defthm
  l6-regular-file-entry-p-correctness-2
  (implies (l6-regular-file-entry-p entry)
           (not (l6-fs-p entry)))
  :hints (("goal" :in-theory (enable l6-regular-file-entry-p)))
  :rule-classes (:rewrite (:rewrite :corollary
  (implies (l6-fs-p entry)
           (not (l6-regular-file-entry-p entry))))))

(defthm alistp-l6-fs-p
  (implies (l6-fs-p fs)
           (alistp fs)))

(defthm l6-fs-p-assoc
  (implies (and (l6-fs-p fs)
                (consp (assoc-equal name fs))
                (not (l6-regular-file-entry-p (cdr (assoc-equal name fs)))))
           (l6-fs-p (cdr (assoc-equal name fs)))))

;; taken from page 18 of the fat overview - the constant 268435448 is written
;; out as 0xFFFFFF8 therein
(defund l6-is-eof (fat-content)
  (declare (xargs :guard (fat32-masked-entry-p fat-content)
                  :guard-hints (("Goal'" :in-theory (enable fat32-masked-entry-p)))))
  (>= fat-content 268435448))

(defthm l6-is-eof-correctness-1
  (implies (< fat-content *ms-bad-cluster*)
           (not (l6-is-eof fat-content)))
  :hints (("Goal" :in-theory (enable l6-is-eof)) ))

;; we have what we need to define a disk traversal to get the contents of the
;; file

;; we're going to make this return a rather literal exit status, as the second
;; element of the mv. that will be 0 if we successfully got a list of indices,
;; and -EIO if we did not for reasons shown in the function
;; fs/fat/cache.c:fat_get_cluster
(defun
    l6-build-index-list
    (fa-table masked-current-cluster length)
  (declare
   (xargs
    :measure (acl2-count length)
    :guard (and (fat32-entry-list-p fa-table)
                (fat32-masked-entry-p masked-current-cluster)
                (natp length)
                (>= masked-current-cluster 2)
                (< masked-current-cluster (len fa-table)))
    :guard-hints
    (("goal"
      :in-theory (disable fat32-entry-mask-correctness-1)
      :use
      (:instance fat32-entry-mask-correctness-1
                 (x (nth masked-current-cluster fa-table)))))))
  (if
      (or (not (integerp length))
          (<= length 0))
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
            (or (l6-is-eof masked-next-cluster)
                (>= masked-next-cluster (len fa-table)))
            (mv (list masked-current-cluster) 0)
          (b*
              (((mv tail-index-list tail-error)
                (l6-build-index-list fa-table masked-next-cluster
                                     (nfix (- length *blocksize*)))))
            (mv (list* masked-current-cluster tail-index-list)
                tail-error)))))))

(defthm l6-build-index-list-correctness-1
  (implies (and (equal b (len fa-table))
                (fat32-masked-entry-p masked-current-cluster)
                (< masked-current-cluster (len fa-table)))
           (b* (((mv index-list &)
                 (l6-build-index-list fa-table
                                      masked-current-cluster length)))
             (bounded-nat-listp index-list b))))

(defthm
  l6-build-index-list-correctness-2
  (implies
   (and
    (fat32-masked-entry-p masked-current-cluster)
    (>= masked-current-cluster 2)
    (< masked-current-cluster (len fa-table)))
   (b* (((mv index-list &)
         (l6-build-index-list fa-table
                              masked-current-cluster length)))
     (fat32-masked-entry-list-p index-list))))

(defthm
  l6-build-index-list-correctness-3
  (b* (((mv & error-code)
        (l6-build-index-list fa-table
                             masked-current-cluster length)))
    (and (integerp error-code)
         (or (equal error-code 0)
             (equal error-code (- *eio*))))))

(defund find-n-free-clusters-helper (fa-table n start)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (natp n)
                              (natp start))))
  (if (or (atom fa-table) (zp n))
      nil
    (if (not (equal (fat32-entry-mask (car fa-table)) 0))
        ;; this block is taken
        (find-n-free-clusters-helper (cdr fa-table) n (+ start 1))
      ;; this block isn't taken
      (cons start (find-n-free-clusters-helper (cdr fa-table) (- n 1) (+ start 1))))))

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

(defund find-n-free-clusters (fa-table n)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (natp n))))
  ;; the first 2 clusters are excluded
  (find-n-free-clusters-helper (nthcdr 2 fa-table) n 2))

(defthm
  find-n-free-clusters-correctness-1
  (implies (and (fat32-entry-list-p fa-table)
                (natp n)
                (equal b (len fa-table))
                (>= (len fa-table) 2))
           (bounded-nat-listp (find-n-free-clusters fa-table n)
                              b))
  :hints (("goal" :in-theory (enable find-n-free-clusters)
           :use ((:instance find-n-free-clusters-helper-correctness-1
                            (start 2)
                            (fa-table (nthcdr 2 fa-table))
                            (b (len fa-table)))))))

(defthm
  find-n-free-clusters-correctness-2
  (nat-listp (find-n-free-clusters fa-table n))
  :hints (("goal" :in-theory (enable find-n-free-clusters
                                     find-n-free-clusters-helper-correctness-2))))

(defthm
  find-n-free-clusters-correctness-3
  (implies (member-equal x (find-n-free-clusters fa-table n))
           (and (integerp x) (<= *ms-first-data-cluster* x)))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters))
   ("goal'"
    :use (:instance find-n-free-clusters-helper-correctness-3
                    (start *ms-first-data-cluster*)
                    (fa-table (nthcdr *ms-first-data-cluster* fa-table))))))

(defthm
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

;; This function allows a file or directory to be found in a filesystem given a
;; path.
(defun l6-stat (hns fs disk)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l6-fs-p fs)
                              (block-listp disk))))
  (if (atom hns)
      fs
    (if (atom fs)
        nil
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            nil
          (if (l6-regular-file-entry-p (cdr sd))
              (and (null (cdr hns))
                   (cdr sd))
            (l6-stat (cdr hns) (cdr sd) disk)))))))

(defthm l6-rdchs-guard-lemma-1
  (implies (and (member-equal x lst)
                (block-listp lst))
           (and (character-listp x)
                (equal (len x) *blocksize*)))
  :rule-classes (:forward-chaining))

;; a note on why this function needs to exist and why it should not replace
;; unmake-blocks
;; unmake-blocks has been used thus far in contexts where the length of the
;; file can be checked to line up with the contents of the file (with only the
;; assumption that the disk satisfies block-listp, nothing more - this is
;; what's checked by feasible-file-length-p)
;; i could have replaced the unmake-blocks function with this one, given that
;; its guard is less restrictive (these clauses are a strict subset of those
;; clauses)
;; i opted not to do so because, in my opinion, the guard verification that
;; takes place with the more restrictive guard is valuable - it shows that
;; we're not leaving room for more than (*blocksize* - 1) characters of junk
;; being added anywhere, as long as we can still verify these things with
;; "local" checks (by which i mean, checks that don't refer too much to the
;; disk, which i consider "not local" for these purposes)
(defun
  unmake-blocks-without-feasibility
  (blocks n)
  (declare (xargs :guard (and (block-listp blocks) (natp n))))
  (mbe
   :exec
   (if
    (atom blocks)
    (make-character-list (take n nil))
    (if
     (< n *blocksize*)
     (take n (car blocks))
     (binary-append
      (car blocks)
      (unmake-blocks-without-feasibility (cdr blocks)
                                         (- n *blocksize*)))))
   :logic
   (if
    (atom blocks)
    (make-character-list (take n nil))
    (let ((head (make-character-list (car blocks))))
         (if (or (not (integerp n)) (< n (len head)))
             (take n head)
             (binary-append head
                            (unmake-blocks-without-feasibility
                             (cdr blocks)
                             (- n (len (car blocks))))))))))

(defthm unmake-blocks-without-feasibility-correctness-1
  (character-listp (unmake-blocks-without-feasibility blocks n)))

(defthm unmake-blocks-without-feasibility-correctness-2
  (equal (len (unmake-blocks-without-feasibility blocks n))
         (nfix n)))

(defthm unmake-blocks-without-feasibility-correctness-3
  (implies (and (block-listp blocks)
                (natp n)
                (feasible-file-length-p (len blocks) n))
           (equal (unmake-blocks-without-feasibility blocks n)
                  (unmake-blocks blocks n)))
  :hints (("goal" :in-theory (enable feasible-file-length-p))
          ("subgoal *1/2''" :expand (len (cdr blocks)))))

(defthm unmake-blocks-without-feasibility-correctness-4
  (implies (and (block-listp blocks) (natp n))
           (iff (consp (unmake-blocks-without-feasibility blocks n))
                (not (equal n 0)))))

(defthm
  unmake-without-feasibility-make-blocks
  (implies
   (and (character-listp text))
   (equal (unmake-blocks-without-feasibility (make-blocks text)
                                             (len text))
          text))
  :hints
  (("subgoal *1/3.2'"
    :in-theory (disable first-n-ac-of-make-character-list)
    :use (:instance first-n-ac-of-make-character-list
                    (i (len text))
                    (l (first-n-ac 8 text nil))
                    (ac nil)))
   ("subgoal *1/3.2'4'"
    :in-theory (disable take-more)
    :use (:instance take-more (i *blocksize*)
                    (l text)
                    (ac1 nil)
                    (ac2 nil)))))

(defund
  l6-file-index-list (file fa-table)
  (declare (xargs :guard (and (l6-regular-file-entry-p file)
                              (fat32-entry-list-p fa-table))))
  (let
      ((first-cluster (l6-regular-file-first-cluster file)))
    (if (or (< first-cluster 2)
            (>= first-cluster (len fa-table)))
        (mv nil 0)
      (l6-build-index-list fa-table first-cluster
                           (l6-regular-file-length file)))))

(defthm
  l6-file-index-list-correctness-1
  (implies (and (l6-regular-file-entry-p file)
                (fat32-entry-list-p fa-table)
                (equal b (len fa-table)))
           (b* (((mv index-list &)
                 (l6-file-index-list file fa-table)))
             (bounded-nat-listp index-list b)))
  :hints (("goal" :in-theory (enable l6-file-index-list))))

(defthm
  l6-file-index-list-correctness-2
  (implies (and (l6-regular-file-entry-p file)
                (fat32-entry-list-p fa-table))
           (b* (((mv index-list &)
                 (l6-file-index-list file fa-table)))
             (fat32-masked-entry-list-p index-list)))
  :hints (("goal" :in-theory (enable l6-file-index-list))))

(defthm
  l6-file-index-list-correctness-3
  (b* (((mv & error-code)
        (l6-file-index-list file fa-table)))
    (and (integerp error-code)
         (or (equal error-code 0)
             (equal error-code (- *eio*)))))
  :hints
  (("goal" :in-theory (enable l6-file-index-list))
   ("Goal'''"
    :in-theory (disable l6-build-index-list-correctness-3)
    :use (:instance l6-build-index-list-correctness-3
                    (masked-current-cluster
                     (l6-regular-file-first-cluster file))
                    (length (l6-regular-file-length file))))))

;; This function finds a text file given its path and reads a segment of
;; that text file.
(defun
  l6-rdchs (hns fs disk fa-table start n)
  (declare
   (xargs
    :guard (and (symbol-listp hns)
                (l6-fs-p fs)
                (natp start)
                (natp n)
                (block-listp disk)
                (fat32-entry-list-p fa-table))
    :guard-hints
    (("subgoal 2.6"
      :in-theory (e/d (fat32-masked-entry-p)
                      (l6-regular-file-entry-p-correctness-1))
      :use (:instance l6-regular-file-entry-p-correctness-1
                      (entry (l6-stat hns fs disk))))
     ("subgoal 3"
      :in-theory (e/d (fat32-masked-entry-p)
                      (l6-regular-file-entry-p-correctness-1))
      :use (:instance l6-regular-file-entry-p-correctness-1
                      (entry (l6-stat hns fs disk)))))))
  (let
   ((file (l6-stat hns fs disk)))
   (if
    (not (l6-regular-file-entry-p file))
    (mv nil (- *EIO*))
    (b*
     (((mv index-list error-code)
       (l6-file-index-list file fa-table))
      (file-text
       (coerce (unmake-blocks-without-feasibility
                (fetch-blocks-by-indices disk index-list)
                (l6-regular-file-length file))
               'string))
      (file-length (length file-text))
      (end (+ start n)))
     (if (< file-length end)
         (mv nil error-code)
         (mv (subseq file-text start (+ start n)) error-code))))))

(defthm
  l6-wrchs-guard-lemma-1
  (implies (and (fat32-masked-entry-p val)
                (fat32-masked-entry-list-p ac))
           (fat32-masked-entry-list-p (make-list-ac n val ac))))

(defthm l6-wrchs-guard-lemma-2
  (implies (true-listp x)
           (equal (fat32-masked-entry-list-p (binary-append x y))
                  (and (fat32-masked-entry-list-p x)
                       (fat32-masked-entry-list-p y)))))

(defthmd
  l6-wrchs-guard-lemma-3
  (equal (fat32-masked-entry-list-p x)
         (bounded-nat-listp x *expt-2-28*))
  :hints (("goal" :in-theory (enable fat32-masked-entry-p))))

(defthm
  l6-wrchs-guard-lemma-4
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
                 (:instance l6-wrchs-guard-lemma-3
                            (x (find-n-free-clusters fa-table n)))
                 (:instance bounded-nat-listp-correctness-5
                            (l (find-n-free-clusters fa-table n))
                            (x (len fa-table))
                            (y *expt-2-28*))))))

;; l6-wrchs and l6-create are in some cases asked to create a zero length file
;; or zero the length of an existing file; the following comment from page 17
;; of the FAT specification applies.

;; Note that a zero-length file a file that has no data allocated to it has a
;; first cluster number of 0 placed in its directory entry.

; This function writes a specified text string to a specified position to a
; text file at a specified path.
(defun
    l6-wrchs
    (hns fs disk fa-table start text)
  (declare
   (xargs
    :guard (and (symbol-listp hns)
                (l6-fs-p fs)
                (natp start)
                (stringp text)
                (block-listp disk)
                (fat32-entry-list-p fa-table)
                (equal (len disk) (len fa-table))
                (<= (len fa-table) *ms-bad-cluster*)
                (>= (len fa-table) 2))))
  (if (atom hns)
      (mv fs disk fa-table (- *enoent*)) ;; error - showed up at fs with no
    ;; name  - so leave fs unchanged
    (if (atom fs)
        (mv nil disk fa-table (- *enoent*)) ;; error, so leave fs unchanged
      (let ((sd (assoc (car hns) fs)))
        (if (atom sd)
            (mv fs disk fa-table (- *enoent*)) ;; file-not-found error, so leave fs unchanged
          (if (l6-regular-file-entry-p (cdr sd))
              (if (cdr hns)
                  (mv (cons (cons (car sd) (cdr sd))
                            (delete-assoc (car hns) fs))
                      disk
                      fa-table (- *enoent*)) ;; error, so leave fs unchanged
                (b* (((mv old-indices read-error-code)
                      (l6-file-index-list (cdr sd) fa-table))
                     (old-text
                      (unmake-blocks-without-feasibility
                       (fetch-blocks-by-indices disk old-indices)
                       (l6-regular-file-length (cdr sd))))
                     (fa-table-after-free
                      (set-indices-in-fa-table
                       fa-table
                       old-indices
                       (make-list (len old-indices) :initial-element 0)))
                     (new-text (insert-text old-text start text))
                     (new-blocks (make-blocks new-text))
                     (new-indices
                      (find-n-free-clusters fa-table-after-free (len new-blocks))))
                  (if (not (equal (len new-indices) (len new-blocks)))
                      ;; we have an error because of insufficient disk space
                      ;; - so we leave the fs unchanged
                      (mv (cons (cons (car sd) (cdr sd))
                                (delete-assoc (car hns) fs))
                          disk
                          fa-table (- *enospc*))
                    (if (consp new-indices)
                        (mv (cons (cons (car sd)
                                        (l6-make-regular-file
                                         (car new-indices)
                                         (len new-text)))
                                  (delete-assoc (car hns) fs))
                            (set-indices disk new-indices new-blocks)
                            (set-indices-in-fa-table fa-table-after-free
                                                     new-indices
                                                     (binary-append
                                                      (cdr new-indices)
                                                      (list *MS-END-OF-CLUSTERCHAIN*))) read-error-code)
                      (mv (cons (cons (car sd)
                                      (l6-make-regular-file
                                       ;; 0 is chosen by default
                                       0
                                       (len new-text)))
                                (delete-assoc (car hns) fs))
                          disk
                          fa-table-after-free
                          read-error-code)))))
            (mv-let (new-contents new-disk new-fa-table error-code)
              (l6-wrchs (cdr hns) (cdr sd) disk fa-table start text)
              (mv (cons (cons (car sd) new-contents)
                        (delete-assoc (car hns) fs))
                  new-disk
                  new-fa-table
                  error-code))))))))

(defun
  l6-create (hns fs disk fa-table text)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l6-fs-p fs)
                              (stringp text)
                              (block-listp disk)
                              (fat32-entry-list-p fa-table)
                              (equal (len disk) (len fa-table))
                              (<= (len fa-table) *ms-bad-cluster*)
                              (>= (len fa-table) 2))))
  (if (atom hns)
      (mv fs disk fa-table) ;; error - showed up at fs with no name  - so leave fs unchanged
    (let ((sd (assoc (car hns) fs)))
      (if (atom sd)
          (if (atom (cdr hns))
              (let* ((blocks (make-blocks (coerce text 'list)))
                     (indices (find-n-free-clusters fa-table (len blocks))))
                (if (not (equal (len indices) (len blocks)))
                    ;; we have an error because of insufficient disk space
                    ;; - so we leave the fs unchanged
                    (mv sd disk fa-table)
                  (if (consp indices)
                      (mv (cons (cons (car hns)
                                      (l6-make-regular-file
                                       (car indices)
                                       (length text)))
                                fs)
                          (set-indices disk indices blocks)
                          (set-indices-in-fa-table fa-table
                                                   indices
                                                   (binary-append
                                                    (cdr indices)
                                                    (list *MS-END-OF-CLUSTERCHAIN*))))
                    (mv (cons (cons (car hns)
                                    (cons indices
                                          (length text)))
                              fs)
                        disk
                        fa-table))))
            (mv-let (new-fs new-disk new-fa-table)
              (l6-create (cdr hns) nil disk fa-table text)
              (mv (cons (cons (car hns) new-fs) fs) new-disk new-fa-table)))
        (let ((contents (cdr sd)))
          (if (l6-regular-file-entry-p contents)
              (mv (cons (cons (car sd) contents) ;; file already exists, so leave fs unchanged
                        (delete-assoc (car hns) fs))
                  disk
                  fa-table)
            (mv-let (new-fs new-disk new-fa-table)
              (l6-create (cdr hns) contents disk fa-table text)
              (mv (cons (cons (car sd)
                              new-fs)
                        (delete-assoc (car hns) fs))
                  new-disk
                  new-fa-table)))
          )))))

; This function deletes a file or directory given its path.
(defun
    l6-unlink (hns fs fa-table)
  (declare (xargs :guard (and (symbol-listp hns)
                              (l6-fs-p fs)
                              (fat32-entry-list-p fa-table)
                              (<= (len fa-table) *ms-bad-cluster*)
                              (>= (len fa-table) 2))))
  (if
      (atom hns)
      (mv fs fa-table (- *ENOENT*)) ;;error case, basically
    (if
        (atom (cdr hns))
        (if
            (and (consp (assoc (car hns) fs))
                 (l6-regular-file-entry-p (cdr (assoc (car hns) fs))))
            (b* (((mv old-indices read-error-code)
                  (l6-file-index-list (cdr (assoc (car hns) fs)) fa-table)))
              (mv
               (delete-assoc (car hns) fs)
               (set-indices-in-fa-table fa-table old-indices
                                        (make-list (len old-indices) :initial-element 0))
               read-error-code))
          (mv
           (delete-assoc (car hns) fs)
           fa-table
           0))
      (if
          (atom fs)
          (mv nil fa-table (- *ENOENT*)) ;; another error case
        (let
            ((sd (assoc (car hns) fs)))
          (if
              (atom sd)
              (mv fs fa-table (- *ENOENT*)) ;; yet another error case
            (let ((contents (cdr sd)))
              (if (l6-regular-file-entry-p contents)
                  (mv fs fa-table (- *enoent*)) ;; we still have names but
                ;; we're at a regular file - error
                (mv-let (new-fs new-fa-table new-error-code)
                  (l6-unlink (cdr hns) contents fa-table)
                  (mv (cons (cons (car sd) new-fs)
                            (delete-assoc (car hns) fs))
                      new-fa-table new-error-code))))))))))

;; From the FAT specification, page 18: "The list of free clusters in the FAT
;; is nothing more than the list of all clusters that contain the value 0 in
;; their FAT cluster entry."
(defund fa-table-to-alv-helper (fa-table)
  (declare (xargs :guard (fat32-entry-list-p fa-table)))
  (if (atom fa-table)
      nil
      (cons (not (equal (fat32-entry-mask (car fa-table))
                        0))
            (fa-table-to-alv-helper (cdr fa-table)))))

(defthm
  fa-table-to-alv-helper-correctness-1
  (equal (len (fa-table-to-alv-helper fa-table))
         (len fa-table))
  :hints (("goal" :in-theory (enable fa-table-to-alv-helper))))

(defthm
  fa-table-to-alv-helper-correctness-2
  (boolean-listp (fa-table-to-alv-helper fa-table))
  :hints (("goal" :in-theory (enable fa-table-to-alv-helper))))

(defthm
  fa-table-to-alv-helper-correctness-3
  (implies
   (and (natp n) (< n (len fa-table)))
   (equal (nth n (fa-table-to-alv-helper fa-table))
          (not (equal (fat32-entry-mask (nth n fa-table))
                      0))))
  :hints (("goal" :in-theory (enable fa-table-to-alv-helper))))

;; The reason why we're having to do this is because we want to assume
;; arbitrary contents in the first two clusters in the fa-table. We could
;; plausibly assume those will be non-zero, but we don't want to.
(defund fa-table-to-alv (fa-table)
  (declare (xargs :guard (and (fat32-entry-list-p fa-table)
                              (<= (len fa-table) *ms-bad-cluster*)
                              (>= (len fa-table) 2))))
  (make-list-ac 2 t (fa-table-to-alv-helper (nthcdr 2 fa-table))))

(defthm
  fa-table-to-alv-correctness-1
  (implies (>= (len fa-table) 2)
           (equal (len (fa-table-to-alv fa-table))
                  (len fa-table)))
  :hints (("goal" :in-theory (enable fa-table-to-alv))))

(defthm
  fa-table-to-alv-correctness-2
  (boolean-listp (fa-table-to-alv fa-table))
  :hints (("goal" :in-theory (enable fa-table-to-alv))))

(defthm
  fa-table-to-alv-correctness-3
  (implies
   (and (integerp n) (>= n 2) (< n (len fa-table)))
   (equal (nth n (fa-table-to-alv fa-table))
          (not (equal (fat32-entry-mask (nth n fa-table))
                      0))))
  :hints (("goal" :in-theory (enable fa-table-to-alv))))

(defun
  l6-to-l4-fs-helper (fs fa-table)
  (declare (xargs :guard (and (l6-fs-p fs)
                              (fat32-entry-list-p fa-table)
                              (<= (len fa-table) *ms-bad-cluster*)
                              (>= (len fa-table) 2))))
  (if
   (atom fs)
   fs
   (let*
    ((directory-or-file-entry (car fs))
     (name (car directory-or-file-entry))
     (entry (cdr directory-or-file-entry)))
    (let
     ((tail-fs (l6-to-l4-fs-helper (cdr fs) fa-table)))
     (if (l6-regular-file-entry-p entry)
         (b* (((mv index-list &)
               (l6-file-index-list entry fa-table)))
           (list* (cons name
                        (cons index-list
                              (l6-regular-file-length entry)))
                  tail-fs))
         (list* (cons name
                      (l6-to-l4-fs-helper entry fa-table))
                tail-fs))))))

(defun
  l6-to-l4-fs (fs fa-table)
  (declare (xargs :verify-guards nil
                  :guard (and (l6-fs-p fs)
                              (fat32-entry-list-p fa-table)
                              (<= (len fa-table) *ms-bad-cluster*)
                              (>= (len fa-table) 2))))
  (mv (l6-to-l4-fs-helper fs fa-table) (fa-table-to-alv fa-table)))

(defthm l6-to-l4-fs-correctness-1
  (implies (and (l6-fs-p fs)
                (fat32-entry-list-p fa-table))
           (mv-let (l4-fs l4-alv) (l6-to-l4-fs fs fa-table)
             (declare (ignore l4-fs))
             (boolean-listp l4-alv))))

(defthm l6-to-l4-fs-correctness-2
  (implies (and (l6-fs-p fs)
                (fat32-entry-list-p fa-table)
                (>= (len fa-table) 2))
           (mv-let (l4-fs l4-alv) (l6-to-l4-fs fs fa-table)
             (declare (ignore l4-fs))
             (equal (len l4-alv) (len fa-table)))))

(verify-guards l6-to-l4-fs)

;; Does (L4-FS-P (MV-NTH 0 (L6-TO-L4-FS FS FA-TABLE))) actually mean much? It
;; just says that file lengths are found to be feasible... after we filter out
;; all the files where they aren't. That's meaningless.

;; It might be better to just make l6-list-all indices return an mv of two
;; values: a list of indices, as in l4, and a boolean value indicating whether
;; any irregular files were found. This is a good idea because it avoids
;; creating two versions of l6-stricter-fs-p, which I specifically do not want
;; to do.

;; This function should return exactly what the helper returned - in addition
;; to a boolean indicating the absence of irregular files
(defund
  l6-list-all-ok-indices (fs fa-table)
  (declare (xargs :verify-guards nil
                  :guard (and (l6-fs-p fs)
                              (fat32-entry-list-p fa-table))))
  (if
   (atom fs)
   (mv nil t)
   (mv-let
     (tail-index-list tail-ok)
     (l6-list-all-ok-indices (cdr fs)
                             fa-table)
     (let*
      ((directory-or-file-entry (car fs))
       (entry (cdr directory-or-file-entry)))
      (if
       (l6-regular-file-entry-p entry)
       (b*
           (((mv head-index-list head-error-code)
             (l6-file-index-list entry fa-table)))
         (if (and (equal head-error-code 0)
                  (feasible-file-length-p
                   (len head-index-list)
                   (l6-regular-file-length entry)))
             (mv (binary-append head-index-list tail-index-list)
                 tail-ok)
             (mv tail-index-list nil)))
       (mv-let
         (head-index-list head-ok)
         (l6-list-all-ok-indices entry fa-table)
         (mv (binary-append head-index-list tail-index-list)
             (and head-ok tail-ok))))))))

(defthm
  l6-list-all-ok-indices-correctness-2
  (mv-let (index-list ok)
    (l6-list-all-ok-indices fs fa-table)
    (declare (ignore index-list))
    (booleanp ok))
  :rule-classes (:type-prescription :rewrite)
  :hints (("goal" :in-theory (enable l6-list-all-ok-indices))))

(defthm
  l6-list-all-ok-indices-correctness-3
  (implies (and (fat32-entry-list-p fa-table)
                (l6-fs-p fs))
           (mv-let (index-list ok)
             (l6-list-all-ok-indices fs fa-table)
             (declare (ignore ok))
             (fat32-masked-entry-list-p index-list)))
  :hints
  (("goal" :in-theory (enable l6-list-all-ok-indices))
   ("subgoal *1/3''"
    :in-theory (disable l6-file-index-list-correctness-2)
    :use ((:instance l6-file-index-list-correctness-2
                     (file (cdr (car fs))))))))

(verify-guards l6-list-all-ok-indices)

(defthm
  l6-list-all-ok-indices-correctness-4
  (implies (and (l6-fs-p fs)
                (fat32-entry-list-p fa-table))
           (b* (((mv & ok)
                 (l6-list-all-ok-indices fs fa-table))
                ((mv l4-fs &)
                 (l6-to-l4-fs fs fa-table)))
             (implies ok (l3-fs-p l4-fs))))
  :hints
  (("goal" :in-theory (enable l6-list-all-ok-indices
                              l3-regular-file-entry-p))
   ("subgoal *1/5'''"
    :in-theory (disable l6-regular-file-entry-p-correctness-1)
    :use (:instance l6-regular-file-entry-p-correctness-1
                    (entry (cdr (car fs)))))
   ("subgoal *1/9'''" :expand (l6-to-l4-fs-helper (cdr (car fs))
                                                  fa-table))))

(defthm
  l6-list-all-ok-indices-correctness-5
  (implies
   (and (l6-fs-p fs)
        (fat32-entry-list-p fa-table))
   (mv-let (l4-fs l4-alv)
     (l6-to-l4-fs fs fa-table)
     (declare (ignore l4-alv))
     (mv-let (index-list ok)
       (l6-list-all-ok-indices fs fa-table)
       (implies ok
                (equal (l4-list-all-indices l4-fs)
                       index-list)))))
  :hints (("Goal" :in-theory (enable L6-LIST-ALL-OK-INDICES L4-LIST-ALL-INDICES
                                     l3-regular-file-entry-p))
          ("Subgoal *1/16''" :expand (l6-to-l4-fs-helper (cdr (car fs))
                                                  fa-table))))

;; What's the file allocation table analog of
;;                 (indices-marked-p all-indices alv)?

;; It would be a proposition that says all these indices which are claimed by
;; the various files are actually used (not 0 or 1) in the file allocation
;; table. But this is, to some extent, self-evident... Except for the first
;; index, which is indicated in the filesystem tree itself, everything else
;; is pointed to by something else.

;; I'm keeping this definition disabled for now because I recall having to
;; disable l4-stricter-fs-p earlier for getting proofs through
(defund l6-stricter-fs-p (fs fa-table)
  (declare (xargs :guard t))
  (and (l6-fs-p fs)
       (fat32-entry-list-p fa-table)
       (mv-let (all-indices ok) (l6-list-all-ok-indices fs fa-table)
         (and ok
              (no-duplicatesp all-indices)))))

(defthm
  l6-stricter-fs-p-correctness-1-lemma-1
  (implies (and (fat32-entry-list-p fa-table)
                (integerp masked-current-cluster)
                (<= 2 masked-current-cluster)
                (< masked-current-cluster (len fa-table)))
           (b* (((mv index-list error-code)
                 (l6-build-index-list fa-table
                                      masked-current-cluster length)))
             (implies (equal error-code 0)
                      (indices-marked-p index-list
                                        (fa-table-to-alv fa-table))))))

(defthm
  l6-stricter-fs-p-correctness-1-lemma-2
  (implies
   (and (l6-regular-file-entry-p entry)
        (fat32-entry-list-p fa-table))
   (b* (((mv index-list error-code)
         (l6-file-index-list entry fa-table)))
     (implies (equal error-code 0)
              (indices-marked-p index-list
                                (fa-table-to-alv fa-table)))))
  :hints (("goal" :in-theory (enable l6-file-index-list))))

(defthm
  l6-stricter-fs-p-correctness-1-lemma-3
  (implies
   (and (l6-fs-p fs)
        (fat32-entry-list-p fa-table)
        (mv-nth 1 (l6-list-all-ok-indices fs fa-table)))
   (indices-marked-p
    (l4-list-all-indices (l6-to-l4-fs-helper fs fa-table))
    (fa-table-to-alv fa-table)))
  :hints
  (("goal" :in-theory (enable l6-list-all-ok-indices
                              l3-regular-file-entry-p))
   ("subgoal *1/16''"
    :expand (l4-list-all-indices
             (cons (cons (car (car fs))
                         (l6-to-l4-fs-helper (cdr (car fs))
                                             fa-table))
                   (l6-to-l4-fs-helper (cdr fs)
                                       fa-table))))
   ("subgoal *1/16'''"
    :expand (l6-to-l4-fs-helper (cdr (car fs))
                                fa-table))
   ("subgoal *1/4''"
    :expand
    (l4-list-all-indices
     (cons (list* (car (car fs))
                  (mv-nth 0
                          (l6-file-index-list (cdr (car fs))
                                              fa-table))
                  (l6-regular-file-length (cdr (car fs))))
           (l6-to-l4-fs-helper (cdr fs) fa-table))))
   ("Subgoal *1/4.1" :in-theory (disable
  l6-stricter-fs-p-correctness-1-lemma-2) :use (:instance
  l6-stricter-fs-p-correctness-1-lemma-2 (entry (CDR (CAR FS)))))))

(defthm
  l6-stricter-fs-p-correctness-1-lemma-4
  (implies
   (and (mv-nth 1 (l6-list-all-ok-indices fs fa-table))
        (l6-fs-p fs)
        (fat32-entry-list-p fa-table))
   (indices-marked-listp (l4-collect-all-index-lists
                          (l6-to-l4-fs-helper fs fa-table))
                         (fa-table-to-alv fa-table)))
  :hints (("goal" :in-theory (enable l6-list-all-ok-indices
                                     l3-regular-file-entry-p))
          ("subgoal *1/10.5'"
           :expand (l6-to-l4-fs-helper (cdr (car fs))
                                       fa-table))))

(defthm
  l6-stricter-fs-p-correctness-1
  (implies (and (l6-fs-p fs)
                (fat32-entry-list-p fa-table))
           (mv-let (l4-fs l4-alv)
             (l6-to-l4-fs fs fa-table)
             (implies (l6-stricter-fs-p fs fa-table)
                      (l4-stricter-fs-p l4-fs l4-alv))))
  :hints
  (("goal"
    :in-theory (e/d (l6-stricter-fs-p l6-list-all-ok-indices)
                    (l4-collect-all-index-lists-correctness-3
                     l6-list-all-ok-indices-correctness-4))
    :use l6-list-all-ok-indices-correctness-4)
   ("goal'''"
    :in-theory (disable l6-list-all-ok-indices-correctness-5)
    :use l6-list-all-ok-indices-correctness-5)))

(defthm
  l6-stricter-fs-p-correctness-2
  (implies (l6-stricter-fs-p fs fa-table)
           (and (l6-fs-p fs)
                (mv-nth 1 (l6-list-all-ok-indices fs fa-table))
                (fat32-entry-list-p fa-table)))
  :hints (("goal" :in-theory (enable l6-stricter-fs-p))))

(defthm
  l6-to-l4-fs-correctness-3
  (implies (and (l6-fs-p fs)
                (mv-nth 1 (l6-list-all-ok-indices fs fa-table))
                (fat32-entry-list-p fa-table))
           (l3-fs-p (l6-to-l4-fs-helper fs fa-table)))
  :hints (("goal" :in-theory (enable l6-list-all-ok-indices
                                     l3-regular-file-entry-p))))

;; Completion semantics for reading and writing still need to be figured out...

(defthm
  l6-stat-correctness-1-lemma-1
  (implies
   (and
    (fat32-entry-list-p fa-table)
    (l6-stricter-fs-p fs fa-table)
    (consp (assoc-equal name fs))
    (not (l6-regular-file-entry-p (cdr (assoc-equal name fs)))))
   (l6-stricter-fs-p (cdr (assoc-equal name fs))
                     fa-table))
  :hints (("goal" :in-theory (enable l6-stricter-fs-p
                                     l6-list-all-ok-indices))))

(defthm
  l6-stat-correctness-1-lemma-2
  (implies
   (and (consp fs)
        (not (l6-regular-file-entry-p (cdr (car fs))))
        (consp (car fs))
        (l6-fs-p (cdr (car fs)))
        (fat32-entry-list-p fa-table))
   (not
    (l3-regular-file-entry-p (l6-to-l4-fs-helper (cdr (car fs))
                                                 fa-table))))
  :hints
  (("goal"
    :expand
    (l3-regular-file-entry-p (l6-to-l4-fs-helper (cdr (car fs))
                                                 fa-table)))
   ("goal'" :expand (l6-to-l4-fs-helper (cdr (car fs))
                                        fa-table))))

(defthm
  l6-stat-correctness-1-lemma-3
  (implies
   (and (l6-fs-p fs)
        (fat32-entry-list-p fa-table)
        (mv-nth 1 (l6-list-all-ok-indices fs fa-table))
        (consp (assoc-equal name fs)))
   (equal (l3-regular-file-entry-p
           (cdr (assoc-equal name (l6-to-l4-fs-helper fs fa-table))))
          (l6-regular-file-entry-p (cdr (assoc-equal name fs)))))
  :hints
  (("goal" :in-theory (enable l6-list-all-ok-indices))
   ("subgoal *1/5" :in-theory (enable l3-regular-file-entry-p))
   ("subgoal *1/4'''"
    :in-theory (enable l3-regular-file-entry-p))))

(defthm
  l6-stat-correctness-1-lemma-4
  (implies
   (and (fat32-entry-list-p fa-table)
        (l6-fs-p fs))
   (equal
    (consp (assoc-equal name
                        (l6-to-l4-fs-helper fs fa-table)))
    (consp (assoc-equal name fs)))))

(defthm
  l6-stat-correctness-1-lemma-5
  (implies
   (and
    (consp (assoc-equal name fs))
    (not
     (l6-regular-file-entry-p (cdr (assoc-equal name fs))))
    (symbolp name)
    (fat32-entry-list-p fa-table)
    (l6-fs-p fs)
    (mv-nth 1 (l6-list-all-ok-indices fs fa-table)))
   (mv-nth
    1
    (l6-list-all-ok-indices (cdr (assoc-equal name fs))
                            fa-table)))
  :hints (("goal" :in-theory (enable l6-list-all-ok-indices))))

(defthm
  l6-stat-correctness-1-lemma-6
  (implies
   (and
    (consp (assoc-equal name fs))
    (not
     (l6-regular-file-entry-p (cdr (assoc-equal name fs))))
    (fat32-entry-list-p fa-table)
    (l6-fs-p fs)
    (no-duplicatesp-equal
     (mv-nth 0
             (l6-list-all-ok-indices fs fa-table))))
   (no-duplicatesp-equal
    (mv-nth 0
            (l6-list-all-ok-indices (cdr (assoc-equal name fs))
                                    fa-table))))
  :hints (("goal" :in-theory (enable l6-list-all-ok-indices))))

(defthm
  l6-stat-correctness-1-lemma-7
  (implies (and (consp (assoc-equal name fs))
                (not (l6-regular-file-entry-p (cdr (assoc-equal name fs))))
                (fat32-entry-list-p fa-table)
                (l6-fs-p fs))
           (equal (cdr (assoc-equal name (l6-to-l4-fs-helper fs fa-table)))
                  (l6-to-l4-fs-helper (cdr (assoc-equal name fs))
                                      fa-table))))

(defthm
  l6-stat-correctness-1-lemma-8
  (implies
   (and (consp (assoc-equal name fs))
        (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
        (fat32-entry-list-p fa-table)
        (l6-fs-p fs))
   (b*
       (((mv index-list &)
         (l6-file-index-list (cdr (assoc-equal name fs))
                             fa-table)))
     (equal
      (cdr (assoc-equal name (l6-to-l4-fs-helper fs fa-table)))
      (cons
       index-list
       (l6-regular-file-length (cdr (assoc-equal name fs))))))))

(defthm
  l6-stat-correctness-1-lemma-9
  (implies
   (and (consp (assoc-equal name fs))
        (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
        (fat32-entry-list-p fa-table)
        (l6-fs-p fs)
        (mv-nth 1 (l6-list-all-ok-indices fs fa-table)))
   (b*
       (((mv index-list &)
         (l6-file-index-list (cdr (assoc-equal name fs))
                             fa-table)))
     (feasible-file-length-p
      (len index-list)
      (l6-regular-file-length (cdr (assoc-equal name fs))))))
  :hints (("goal" :in-theory (enable l6-list-all-ok-indices))))

(defthm
  l6-stat-correctness-1-lemma-10
  (implies
   (l6-fs-p fs)
   (equal (consp (l6-to-l4-fs-helper fs fa-table))
          (consp fs))))

;; This is the first of two theorems showing the equivalence of the l6 and l4
;; versions of stat.
(defthm
  l6-stat-correctness-1
  (implies
   (and (symbol-listp hns)
        (block-listp disk)
        (fat32-entry-list-p fa-table)
        (l6-fs-p fs)
        (mv-nth 1 (l6-list-all-ok-indices fs fa-table))
        (no-duplicatesp-equal
         (mv-nth 0 (l6-list-all-ok-indices fs fa-table)))
        (l6-regular-file-entry-p (l6-stat hns fs disk)))
   (b* (((mv file-index-list &)
       (l6-file-index-list (l6-stat hns fs disk)
                           fa-table)) )
   (equal
    (l3-stat hns (l6-to-l4-fs-helper fs fa-table)
             disk)
    (implode
     (unmake-blocks
      (fetch-blocks-by-indices
       disk
       file-index-list)
      (l6-regular-file-length (l6-stat hns fs disk)))))))
  :hints (("goal" :in-theory (enable l6-stricter-fs-p))
          ("subgoal *1/4'''"
           :in-theory (enable l3-regular-file-entry-p))
          ("subgoal *1/11.2'"
           :in-theory (enable l3-regular-file-entry-p)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (symbol-listp hns)
          (block-listp disk)
          (fat32-entry-list-p fa-table)
          (l6-stricter-fs-p fs fa-table))
     (b*
         (((mv l4-fs &) (l6-to-l4-fs fs fa-table))
          (l6-file (l6-stat hns fs disk))
          ((mv file-index-list &) (l6-file-index-list l6-file fa-table)))
       (implies
        (l6-regular-file-entry-p l6-file)
        (equal
         (l3-stat hns l4-fs disk)
         (coerce (unmake-blocks
                  (fetch-blocks-by-indices
                   disk
                   file-index-list)
                  (l6-regular-file-length l6-file))
                 'string)))))
    :hints (("goal" :in-theory (enable l6-stricter-fs-p))))))

;; This is the second of two theorems showing the equivalence of the l6 and l4
;; versions of stat.
(defthm
  l6-stat-correctness-2
  (implies (and (symbol-listp hns)
                (fat32-entry-list-p fa-table)
                (l6-stricter-fs-p fs fa-table)
                (block-listp disk)
                (l6-fs-p (l6-stat hns fs disk)))
           (equal (l3-stat hns (l6-to-l4-fs-helper fs fa-table)
                           disk)
                  (l6-to-l4-fs-helper (l6-stat hns fs disk)
                                      fa-table)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (symbol-listp hns)
          (fat32-entry-list-p fa-table)
          (l6-stricter-fs-p fs fa-table)
          (block-listp disk)
          (l6-fs-p (l6-stat hns fs disk)))
     (b*
         (((mv l4-fs &) (l6-to-l4-fs fs fa-table))
          (l6-fs (l6-stat hns fs disk)))
       (implies (l6-fs-p l6-fs)
                (equal (l3-stat hns l4-fs disk)
                       (mv-nth 0
                               (l6-to-l4-fs (l6-stat hns fs disk)
                                            fa-table))))))))
  :hints
  (("goal" :in-theory (enable l6-stricter-fs-p))
   ("subgoal *1/5''"
    :in-theory (enable l3-regular-file-entry-p))
   ("subgoal *1/11.2'"
    :in-theory (disable l6-stat-correctness-1-lemma-3)
    :use (:instance l6-stat-correctness-1-lemma-3
                    (name (car hns))))
   ("subgoal *1/11.1'"
    :in-theory (disable l6-stat-correctness-1-lemma-3)
    :use (:instance l6-stat-correctness-1-lemma-3
                    (name (car hns))))))

(defthm
  l6-rdchs-correctness-1-lemma-1
  (implies
   (and (l6-fs-p fs)
        (fat32-entry-list-p fa-table)
        (mv-nth 1 (l6-list-all-ok-indices fs fa-table))
        (no-duplicatesp-equal (mv-nth 0 (l6-list-all-ok-indices fs fa-table)))
        (symbol-listp hns)
        (block-listp disk))
   (equal (stringp (l3-stat hns (l6-to-l4-fs-helper fs fa-table)
                            disk))
          (l6-regular-file-entry-p (l6-stat hns fs disk))))
  :hints (("goal" :in-theory (enable l6-stricter-fs-p))
          ("Subgoal *1/5''" :in-theory (enable L3-REGULAR-FILE-ENTRY-P))
          ("Subgoal *1/4.1'" :in-theory (enable L3-REGULAR-FILE-ENTRY-P))
          ("Subgoal *1/10.2'"
           :in-theory (disable l6-stat-correctness-1-lemma-3)
           :use (:instance l6-stat-correctness-1-lemma-3
                           (name (car hns))))
          ("Subgoal *1/10.1'"
           :in-theory (disable l6-stat-correctness-1-lemma-3)
           :use (:instance l6-stat-correctness-1-lemma-3
                           (name (car hns))))))

;; This lemma should be where unmake-blocks is defined - it isn't, currently,
;; because placing it there leaves us with a beast of a proof-builder lemma to
;; debug in file-system-4.lisp (which shouldn't be reliant on the proof builder
;; in the first place - oh well)
(defthm
  unmake-blocks-correctness-2
  (implies (and (block-listp blocks)
                (natp n)
                (feasible-file-length-p (len blocks) n))
           (equal (len (unmake-blocks blocks n))
                  n))
  :rule-classes
  ((:rewrite :corollary (implies (and (block-listp blocks)
                                      (natp n)
                                      (feasible-file-length-p (len blocks) n))
                                 (iff (consp (unmake-blocks blocks n))
                                      (not (zp n))))))
  :hints (("goal" :in-theory (enable feasible-file-length-p))
          ("subgoal *1/5'''" :expand (len (cdr blocks)))))

(defthm
  l6-rdchs-correctness-1-lemma-2
  (implies
   (and (l6-stricter-fs-p fs fa-table)
        (fat32-entry-list-p fa-table)
        (symbol-listp hns)
        (block-listp disk)
        (l6-regular-file-entry-p (l6-stat hns fs disk))
        (<= 0
            (l6-regular-file-length (l6-stat hns fs disk))))
   (b*
       (((mv file-index-list &)
         (l6-file-index-list (l6-stat hns fs disk)
                             fa-table)))
     (equal
      (len (unmake-blocks
            (fetch-blocks-by-indices disk file-index-list)
            (l6-regular-file-length (l6-stat hns fs disk))))
      (l6-regular-file-length (l6-stat hns fs disk)))))
  :hints
  (("goal" :in-theory (enable l6-stricter-fs-p))
   ("subgoal *1/4'''"
    :in-theory (enable unmake-blocks-correctness-2)
    :use
    (:instance
     unmake-blocks-correctness-2
     (blocks
      (fetch-blocks-by-indices
       disk
       (mv-nth
        0
        (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                            fa-table))))
     (n (l6-regular-file-length
         (cdr (assoc-equal (car hns) fs))))))))

(defthm
  l6-rdchs-correctness-1-lemma-3
  (implies
   (and (l6-stricter-fs-p fs fa-table)
        (fat32-entry-list-p fa-table)
        (symbol-listp hns)
        (block-listp disk)
        (l6-regular-file-entry-p (l6-stat hns fs disk)))
   (b* (((mv file-index-list &)
         (l6-file-index-list (l6-stat hns fs disk)
                             fa-table)))
     (feasible-file-length-p
      (len file-index-list)
      (l6-regular-file-length (l6-stat hns fs disk)))))
  :hints (("goal" :in-theory (enable l6-stricter-fs-p))))

(defthm
  l6-rdchs-correctness-1
  (implies
   (and (l6-stricter-fs-p fs fa-table)
        (natp start)
        (natp n)
        (fat32-entry-list-p fa-table)
        (symbol-listp hns)
        (block-listp disk))
   (mv-let (l4-fs l4-alv)
     (l6-to-l4-fs fs fa-table)
     (declare (ignore l4-alv))
     (equal (l4-rdchs hns l4-fs disk start n)
            (mv-nth 0 (l6-rdchs hns fs disk fa-table start n)))))
  :hints (("goal" :in-theory (enable l6-stricter-fs-p))))

(defthm l6-wrchs-returns-fs-lemma-1
  (implies (and (l6-fs-p fs))
           (l6-fs-p (delete-assoc-equal name fs))))

;; This obviously needs clean up - I'm just trying to get past an infinite loop
;; in ACL2
(defthm
  l6-wrchs-returns-fs-lemma-2
  (implies
   (and
    (consp (assoc-equal name fs))
    (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
    (consp (l6-file-index-list (cdr (assoc-equal name fs))
                               fa-table))
    (< (car (l6-file-index-list (cdr (assoc-equal name fs))
                                fa-table))
       (len disk))
    (consp
     (find-n-free-clusters
      (update-nth
       (car (l6-file-index-list (cdr (assoc-equal name fs))
                                fa-table))
       (fat32-update-lower-28
        (nth
         (car (l6-file-index-list (cdr (assoc-equal name fs))
                                  fa-table))
         fa-table)
        0)
       fa-table)
      (len
       (make-blocks
        (insert-text
         (unmake-blocks-without-feasibility
          (fetch-blocks-by-indices
           disk
           (l6-file-index-list (cdr (assoc-equal name fs))
                               fa-table))
          (l6-regular-file-length (cdr (assoc-equal name fs))))
         start text)))))
    (l6-fs-p fs)
    (integerp start)
    (<= 0 start)
    (stringp text)
    (block-listp disk)
    (fat32-entry-list-p fa-table)
    (equal (len disk) (len fa-table))
    (<= (len fa-table) *ms-bad-cluster*)
    (<= 2 (len fa-table)))
   (l6-regular-file-entry-p
    (l6-make-regular-file
     (car
      (find-n-free-clusters
       (update-nth
        (car (l6-file-index-list (cdr (assoc-equal name fs))
                                 fa-table))
        (fat32-update-lower-28
         (nth
          (car (l6-file-index-list (cdr (assoc-equal name fs))
                                   fa-table))
          fa-table)
         0)
        fa-table)
       (len
        (make-blocks
         (insert-text
          (unmake-blocks-without-feasibility
           (fetch-blocks-by-indices
            disk
            (l6-file-index-list (cdr (assoc-equal name fs))
                                fa-table))
           (l6-regular-file-length (cdr (assoc-equal name fs))))
          start text)))))
     (len
      (insert-text
       (unmake-blocks-without-feasibility
        (fetch-blocks-by-indices
         disk
         (l6-file-index-list (cdr (assoc-equal name fs))
                             fa-table))
        (l6-regular-file-length (cdr (assoc-equal name fs))))
       start text)))))
  :hints
  (("goal"
    :in-theory (disable l6-make-regular-file-correctness-1
                        l6-wrchs-guard-lemma-4)
    :use
    ((:instance
      l6-make-regular-file-correctness-1
      (first-cluster
       (car
        (find-n-free-clusters
         (update-nth
          (car (l6-file-index-list (cdr (assoc-equal name fs))
                                   fa-table))
          (fat32-update-lower-28
           (nth
            (car (l6-file-index-list (cdr (assoc-equal name fs))
                                     fa-table))
            fa-table)
           0)
          fa-table)
         (len
          (make-blocks
           (insert-text
            (unmake-blocks-without-feasibility
             (fetch-blocks-by-indices
              disk
              (l6-file-index-list (cdr (assoc-equal name fs))
                                  fa-table))
             (l6-regular-file-length
              (cdr (assoc-equal name fs))))
            start text))))))
      (length
       (len
        (insert-text
         (unmake-blocks-without-feasibility
          (fetch-blocks-by-indices
           disk
           (l6-file-index-list (cdr (assoc-equal name fs))
                               fa-table))
          (l6-regular-file-length (cdr (assoc-equal name fs))))
         start text))))
     (:instance
      l6-wrchs-guard-lemma-4
      (fa-table
       (update-nth
        (car (l6-file-index-list (cdr (assoc-equal name fs))
                                 fa-table))
        (fat32-update-lower-28
         (nth
          (car (l6-file-index-list (cdr (assoc-equal name fs))
                                   fa-table))
          fa-table)
         0)
        fa-table))
      (n
       (len
        (make-blocks
         (insert-text
          (unmake-blocks-without-feasibility
           (fetch-blocks-by-indices
            disk
            (l6-file-index-list (cdr (assoc-equal name fs))
                                fa-table))
           (l6-regular-file-length (cdr (assoc-equal name fs))))
          start text)))))))
   ("subgoal 8"
    :in-theory (disable set-indices-in-fa-table-guard-lemma-1)
    :use
    (:instance
     set-indices-in-fa-table-guard-lemma-1
     (key (car (l6-file-index-list (cdr (assoc-equal name fs))
                                   fa-table)))
     (val
      (fat32-update-lower-28
       (nth (car (l6-file-index-list (cdr (assoc-equal name fs))
                                     fa-table))
            fa-table)
       0))
     (l fa-table)))))

(defthm
  l6-wrchs-returns-fs
  (implies (and (symbol-listp hns)
                (l6-fs-p fs)
                (natp start)
                (stringp text)
                (block-listp disk)
                (fat32-entry-list-p fa-table)
                (equal (len disk) (len fa-table))
                (<= (len fa-table) *ms-bad-cluster*)
                (>= (len fa-table) 2))
           (b* (((mv new-fs & &)
                 (l6-wrchs hns fs disk fa-table start text)))
             (l6-fs-p new-fs)))
  :hints
  (("subgoal *1/6.1'"
    :in-theory (disable l6-wrchs-guard-lemma-4)
    :use
    ((:instance
      l6-wrchs-guard-lemma-4
      (fa-table
       (update-nth
        (car
         (mv-nth
          0
          (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                              fa-table)))
        (fat32-update-lower-28
         (nth
          (car
           (mv-nth
            0
            (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                fa-table)))
          fa-table)
         0)
        fa-table))
      (n
       (len
        (make-blocks
         (insert-text
          (unmake-blocks-without-feasibility
           (fetch-blocks-by-indices
            disk
            (mv-nth 0
                    (l6-file-index-list
                     (cdr (assoc-equal (car hns) fs))
                     fa-table)))
           (l6-regular-file-length
            (cdr (assoc-equal (car hns) fs))))
          start text)))))))))

(defthm
  l6-wrchs-correctness-1-lemma-5
  (implies
   (and (consp (assoc-equal name fs))
        (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
        (l6-fs-p fs)
        (fat32-entry-list-p fa-table)
        (mv-nth 1 (l6-list-all-ok-indices fs fa-table)))
   (equal
    (delete-assoc-equal name (l6-to-l4-fs-helper fs fa-table))
    (l6-to-l4-fs-helper (delete-assoc-equal name fs)
                        fa-table)))
  :hints (("goal" :in-theory (enable l6-list-all-ok-indices)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (consp (assoc-equal name fs))
          (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
          (l6-stricter-fs-p fs fa-table)
          (fat32-entry-list-p fa-table))
     (equal
      (delete-assoc-equal name (l6-to-l4-fs-helper fs fa-table))
      (l6-to-l4-fs-helper (delete-assoc-equal name fs)
                          fa-table)))
    :hints (("goal" :in-theory (enable l6-stricter-fs-p))))))

(defthm
  l6-wrchs-correctness-1-lemma-6
  (implies
   (and (consp (assoc-equal name fs))
        (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
        (l6-stricter-fs-p fs fa-table)
        (fat32-entry-list-p fa-table))
   (l3-regular-file-entry-p
    (cons
     (mv-nth 0
             (l6-file-index-list (cdr (assoc-equal name fs))
                                 fa-table))
     (l6-regular-file-length (cdr (assoc-equal name fs))))))
  :hints (("goal" :in-theory (enable l3-regular-file-entry-p
                                     l6-stricter-fs-p))))

(defthm
  l6-wrchs-correctness-1-lemma-9
  (implies
   (and (natp start)
        (natp n)
        (fat32-entry-list-p fa-table)
        (<= 2 (len fa-table)))
   (equal (find-n-free-blocks-helper (make-list-ac n t ac)
                                     m start)
          (find-n-free-blocks-helper ac m (+ n start))))
  :hints
  (("goal" :in-theory (enable find-n-free-blocks-helper))))

(defthm
  l6-wrchs-correctness-1-lemma-10
  (implies
   (and (fat32-entry-list-p fa-table))
   (equal
    (find-n-free-blocks-helper (fa-table-to-alv-helper fa-table)
                               n start)
    (find-n-free-clusters-helper fa-table n start)))
  :hints
  (("goal" :in-theory (enable find-n-free-clusters-helper
                              fa-table-to-alv-helper
                              find-n-free-blocks-helper))))

(defthm
  l6-wrchs-correctness-1-lemma-8
  (implies (and (fat32-entry-list-p fa-table)
                (>= (len fa-table) 2))
           (equal (find-n-free-blocks (fa-table-to-alv fa-table)
                                      n)
                  (find-n-free-clusters fa-table n)))
  :hints
  (("goal"
    :in-theory (enable find-n-free-clusters
                       fa-table-to-alv find-n-free-blocks))))

(defthm
  l6-wrchs-correctness-1-lemma-7
  (implies
   (and (>= (len fa-table) 2)
        (fat32-entry-list-p fa-table)
        (natp n))
   (equal (len (find-n-free-clusters fa-table n))
          (min (count-free-blocks (fa-table-to-alv fa-table)) n)))
  :hints
  (("goal" :in-theory (disable l6-wrchs-correctness-1-lemma-8)
    :use l6-wrchs-correctness-1-lemma-8)))

(defthm
  l6-wrchs-correctness-1-lemma-13
  (implies
   (natp key)
   (equal (fa-table-to-alv-helper (update-nth key val fa-table))
          (update-nth key
                      (not (equal (fat32-entry-mask val) 0))
                      (fa-table-to-alv-helper fa-table))))
  :hints (("goal" :in-theory (enable fa-table-to-alv-helper))))

(defthm
  l6-wrchs-correctness-1-lemma-12
  (implies
   (and (integerp key) (>= key 2))
   (equal (fa-table-to-alv (update-nth key val fa-table))
          (update-nth key
                      (not (equal (fat32-entry-mask val) 0))
                      (fa-table-to-alv fa-table))))
  :hints (("goal" :in-theory (enable fa-table-to-alv))))

(defthmd
  l6-wrchs-correctness-1-lemma-15
  (implies
   (and (fat32-entry-list-p fa-table)
        (fat32-masked-entry-p masked-current-cluster)
        (natp length)
        (>= masked-current-cluster 2)
        (< masked-current-cluster (len fa-table))
        (member-equal
         x
         (mv-nth 0
                 (l6-build-index-list fa-table
                                      masked-current-cluster length))))
   (and (integerp x) (>= x 2)))
  :hints (("goal" :in-theory (enable l6-build-index-list))))

(defthm
  l6-wrchs-correctness-1-lemma-14
  (implies
   (and (l6-regular-file-entry-p file)
        (fat32-entry-list-p fa-table)
        (member-equal
         x
         (mv-nth 0 (l6-file-index-list file fa-table))))
   (and (integerp x) (>= x 2)))
  :hints
  (("goal"
    :in-theory (enable l6-file-index-list)
    :use (:instance l6-wrchs-correctness-1-lemma-15
                    (masked-current-cluster
                     (l6-regular-file-first-cluster file))
                    (length (l6-regular-file-length file))))))

(defthm
  l6-wrchs-correctness-1-lemma-17
  (implies
   (and (l6-regular-file-entry-p file)
        (feasible-file-length-p
         (len (mv-nth 0 (l6-file-index-list file fa-table)))
         (l6-regular-file-length file)))
   (iff (consp (mv-nth 0 (l6-file-index-list file fa-table)))
        (not (equal (l6-regular-file-length file)
                    0))))
  :hints
  (("goal" :in-theory (enable feasible-file-length-p))
   ("subgoal 1"
    :expand (len (mv-nth 0
                         (l6-file-index-list file fa-table))))))

(defthm
  l6-wrchs-correctness-1-lemma-16
  (implies
   (and
    (consp (assoc-equal name fs))
    (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
    (not
     (consp
      (mv-nth 0
              (l6-file-index-list (cdr (assoc-equal name fs))
                                  fa-table))))
    (consp
     (find-n-free-clusters
      fa-table
      (len
       (make-blocks
        (insert-text
         (make-character-list
          (first-n-ac
           (l6-regular-file-length (cdr (assoc-equal name fs)))
           nil nil))
         start text)))))
    (l6-stricter-fs-p fs fa-table)
    (fat32-entry-list-p fa-table)
    (stringp text)
    (integerp start)
    (<= 0 start)
    (<= 2 (len fa-table))
    (<= (len (make-blocks (insert-text nil start text)))
        (count-free-blocks (fa-table-to-alv fa-table))))
   (equal
    (len
     (find-n-free-clusters
      fa-table
      (len
       (make-blocks
        (insert-text
         (make-character-list
          (first-n-ac
           (l6-regular-file-length (cdr (assoc-equal name fs)))
           nil nil))
         start text)))))
    (len
     (make-blocks
      (insert-text
       (make-character-list
        (first-n-ac
         (l6-regular-file-length (cdr (assoc-equal name fs)))
         nil nil))
       start text))))))

(defthm
  l6-wrchs-correctness-1-lemma-18
  (implies
   (and
    (consp (assoc-equal name fs))
    (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
    (l6-stricter-fs-p fs fa-table)
    (fat32-entry-list-p fa-table)
    (<= 2 (len fa-table)))
   (l3-regular-file-entry-p
    (cdr (assoc-equal name
                      (l6-to-l4-fs-helper fs fa-table))))))

;; We cannot reason with find-n-free-clusters and find-n-free clusters-helper
;; here. We're going to have to abstract away its properties and treat it like
;; a list of integers, all greater than equal to 2, all less than the length of
;; the disk.

;; This might also be a good time to add a constant in place of 2. I don't like
;; the idea of considering 2 to be special here.

(defund lower-bounded-integer-listp (l b)
  (declare (xargs :guard (integerp b)))
  (if (atom l)
      (equal l nil)
    (and (integerp (car l)) (>= (car l) b) (lower-bounded-integer-listp (cdr l) b))))

(defthm lower-bounded-integer-listp-correctness-2
  (implies (true-listp x)
           (equal (lower-bounded-integer-listp (binary-append x y)
                                     b)
                  (and (lower-bounded-integer-listp x b)
                       (lower-bounded-integer-listp y b))))
  :hints (("Goal" :in-theory (enable lower-bounded-integer-listp))))

(defthmd lower-bounded-integer-listp-correctness-5
  (implies (and (<= y x) (lower-bounded-integer-listp l x))
           (lower-bounded-integer-listp l y))
  :hints (("Goal" :in-theory (enable lower-bounded-integer-listp))))

(defthm
  l6-wrchs-correctness-1-lemma-48
  (implies
   (and (fat32-entry-list-p fa-table)
        (>= (len fa-table)
            *ms-first-data-cluster*)
        (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list))
        (lower-bounded-integer-listp index-list *ms-first-data-cluster*)
        (bounded-nat-listp index-list (len fa-table))
        (lower-bounded-integer-listp value-list *ms-first-data-cluster*))
   (equal
    (fa-table-to-alv (set-indices-in-fa-table fa-table index-list value-list))
    (set-indices-in-alv (fa-table-to-alv fa-table)
                        index-list t)))
  :hints
  (("goal" :in-theory (enable set-indices-in-fa-table
                              lower-bounded-integer-listp)
    :induct (set-indices-in-fa-table fa-table index-list value-list))
   ("subgoal *1/1''" :in-theory (enable set-indices-in-alv))
   ("subgoal *1/3.4'" :in-theory (e/d (set-indices-in-alv)))))

(defthm
  l6-wrchs-correctness-1-lemma-49
  (implies
   (and (consp (assoc-equal name fs))
        (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
        (l6-stricter-fs-p fs fa-table))
   (indices-marked-p
    (mv-nth 0
            (l6-file-index-list (cdr (assoc-equal name fs))
                                fa-table))
    (fa-table-to-alv fa-table)))
  :hints (("goal" :in-theory (enable l6-stricter-fs-p
                                     l6-list-all-ok-indices))))

(defthm
  l6-wrchs-correctness-1-lemma-50
  (implies
   (and (consp (assoc-equal name fs))
        (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
        (l6-stricter-fs-p fs fa-table))
   (no-duplicatesp-equal
              (mv-nth 0
                      (l6-file-index-list (cdr (assoc-equal name fs))
                                          fa-table))))
  :hints (("goal" :in-theory (enable l6-stricter-fs-p
                                     l6-list-all-ok-indices))))

(defthm
  l6-wrchs-correctness-1-lemma-51
  (implies
   (and (< key (len fa-table))
        (<= *ms-first-data-cluster* key)
        (<= *ms-first-data-cluster* (len fa-table))
        (fat32-entry-list-p fa-table)
        (natp key)
        (fat32-entry-p val)
        (equal (fat32-entry-mask val) 0))
   (equal (fa-table-to-alv (update-nth key val fa-table))
          (update-nth key nil (fa-table-to-alv fa-table))))
  :hints (("goal" :in-theory (enable fa-table-to-alv))))

(encapsulate
  ()

  (local (include-book "std/lists/repeat" :dir :system))

  (defthm
    l6-wrchs-correctness-1-lemma-19
    (implies
     (and (<= *ms-first-data-cluster* (len fa-table))
          (fat32-entry-list-p fa-table)
          (lower-bounded-integer-listp
           index-list *ms-first-data-cluster*)
          (bounded-nat-listp index-list (len fa-table)))
     (equal (fa-table-to-alv
             (set-indices-in-fa-table
              fa-table index-list
              (make-list-ac (len index-list) 0 nil)))
            (set-indices-in-alv (fa-table-to-alv fa-table)
                                index-list nil)))
    :hints
    (("goal''"
      :in-theory (enable set-indices-in-fa-table)
      :induct (set-indices-in-fa-table
               fa-table index-list
               (make-list-ac (len index-list) 0 nil)))
     ("subgoal *1/7'''"
      :in-theory
      (e/d (set-indices-in-alv lower-bounded-integer-listp)
           (l6-wrchs-correctness-1-lemma-51))
      :use
      (:instance
       l6-wrchs-correctness-1-lemma-51
       (key (car index-list))
       (val
        (fat32-update-lower-28 (nth (car index-list) fa-table)
                               0)))
      :expand (set-indices (fa-table-to-alv fa-table)
                           index-list
                           (repeat (+ 1 (len (cdr index-list)))
                                   nil)))
     ("subgoal *1/5''"
      :in-theory
      (e/d (set-indices-in-alv lower-bounded-integer-listp)
           (l6-wrchs-correctness-1-lemma-51))
      :use
      (:instance
       l6-wrchs-correctness-1-lemma-51
       (key (car index-list))
       (val
        (fat32-update-lower-28 (nth (car index-list) fa-table)
                               0)))
      :expand (set-indices (fa-table-to-alv fa-table)
                           index-list
                           (repeat (+ 1 (len (cdr index-list)))
                                   nil)))
     ("subgoal *1/1'''" :in-theory (enable set-indices-in-alv)))))

(defthm
  l6-wrchs-correctness-1-lemma-52
  (implies
   (and (fat32-entry-list-p fa-table)
        (fat32-masked-entry-p masked-current-cluster)
        (natp length)
        (>= masked-current-cluster 2)
        (< masked-current-cluster (len fa-table)))
   (lower-bounded-integer-listp
    (mv-nth 0
            (l6-build-index-list
             fa-table masked-current-cluster length))
    *ms-first-data-cluster*))
  :hints
  (("goal" :in-theory (enable l6-build-index-list
                              lower-bounded-integer-listp))))

(defthm
  l6-wrchs-correctness-1-lemma-53
  (implies
   (and (consp (assoc-equal name fs))
        (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
        (l6-stricter-fs-p fs fa-table))
   (lower-bounded-integer-listp
    (mv-nth 0
            (l6-file-index-list (cdr (assoc-equal name fs))
                                fa-table))
    *ms-first-data-cluster*))
  :hints (("goal" :in-theory (enable l6-file-index-list))))

(defthm
  l6-wrchs-correctness-1-lemma-20
  (implies
   (and
    (consp (assoc-equal name fs))
    (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
    (l6-stricter-fs-p fs fa-table)
    (fat32-entry-list-p fa-table)
    (stringp text)
    (integerp start)
    (<= 0 start)
    (<= (len fa-table) *ms-bad-cluster*)
    (<= *ms-first-data-cluster* (len fa-table))
    (<= (len (make-blocks (insert-text nil start text)))
        (count-free-blocks (fa-table-to-alv fa-table)))
    (>=
     (count-free-blocks
      (set-indices-in-alv
       (fa-table-to-alv fa-table)
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal name fs))
                                   fa-table))
       nil))
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (mv-nth
           0
           (l6-file-index-list (cdr (assoc-equal name fs))
                               fa-table)))
         (l6-regular-file-length (cdr (assoc-equal name fs))))
        start text)))))
   (equal
    (len
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal name fs))
                                   fa-table))
       (make-list-ac
        (len
         (mv-nth 0
                 (l6-file-index-list (cdr (assoc-equal name fs))
                                     fa-table)))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth
            0
            (l6-file-index-list (cdr (assoc-equal name fs))
                                fa-table)))
          (l6-regular-file-length (cdr (assoc-equal name fs))))
         start text)))))
    (len
     (make-blocks
      (insert-text
       (unmake-blocks
        (fetch-blocks-by-indices
         disk
         (mv-nth 0
                 (l6-file-index-list (cdr (assoc-equal name fs))
                                     fa-table)))
        (l6-regular-file-length (cdr (assoc-equal name fs))))
       start text)))))
  :hints
  (("goal"
    :in-theory (disable l6-wrchs-correctness-1-lemma-7
                        l4-wrchs-correctness-1-lemma-18)
    :use
    ((:instance
      l6-wrchs-correctness-1-lemma-7
      (fa-table
       (set-indices-in-fa-table
        fa-table
        (mv-nth 0
                (l6-file-index-list (cdr (assoc-equal name fs))
                                    fa-table))
        (make-list-ac
         (len
          (mv-nth
           0
           (l6-file-index-list (cdr (assoc-equal name fs))
                               fa-table)))
         0 nil)))
      (n
       (len
        (make-blocks
         (insert-text
          (unmake-blocks
           (fetch-blocks-by-indices
            disk
            (mv-nth
             0
             (l6-file-index-list (cdr (assoc-equal name fs))
                                 fa-table)))
           (l6-regular-file-length (cdr (assoc-equal name fs))))
          start text)))))
     (:instance
      l4-wrchs-correctness-1-lemma-18
      (alv (fa-table-to-alv fa-table))
      (index-list
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal name fs))
                                   fa-table))))))
   ("goal'''"
    :in-theory (disable
                        l6-wrchs-correctness-1-lemma-19)
    :use
    ((:instance
      l6-wrchs-correctness-1-lemma-19
      (index-list
            (MV-NTH 0
                    (L6-FILE-INDEX-LIST (CDR (ASSOC-EQUAL NAME FS))
                                        FA-TABLE))))))))

(defthm
  l6-wrchs-correctness-1-lemma-21
  (implies
   (and
    (consp (assoc-equal name fs))
    (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
    (consp
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal name fs))
                                   fa-table))
       (make-list-ac
        (len
         (mv-nth 0
                 (l6-file-index-list (cdr (assoc-equal name fs))
                                     fa-table)))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth
            0
            (l6-file-index-list (cdr (assoc-equal name fs))
                                fa-table)))
          (l6-regular-file-length (cdr (assoc-equal name fs))))
         start text)))))
    (l6-stricter-fs-p fs fa-table)
    (fat32-entry-list-p fa-table)
    (stringp text)
    (integerp start)
    (<= 0 start)
    (symbolp name)
    (<= (len fa-table) *ms-bad-cluster*)
    (<= 2 (len fa-table))
    (<= (len (make-blocks (insert-text nil start text)))
        (count-free-blocks (fa-table-to-alv fa-table)))
    (equal
     (len
      (find-n-free-blocks
       (set-indices-in-alv
        (fa-table-to-alv fa-table)
        (mv-nth 0
                (l6-file-index-list (cdr (assoc-equal name fs))
                                    fa-table))
        nil)
       (len
        (make-blocks
         (insert-text
          (unmake-blocks
           (fetch-blocks-by-indices
            disk
            (mv-nth
             0
             (l6-file-index-list (cdr (assoc-equal name fs))
                                 fa-table)))
           (l6-regular-file-length (cdr (assoc-equal name fs))))
          start text)))))
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (mv-nth
           0
           (l6-file-index-list (cdr (assoc-equal name fs))
                               fa-table)))
         (l6-regular-file-length (cdr (assoc-equal name fs))))
        start text)))))
   (equal
    (find-n-free-blocks
     (set-indices-in-alv
      (fa-table-to-alv fa-table)
      (mv-nth 0
              (l6-file-index-list (cdr (assoc-equal name fs))
                                  fa-table))
      nil)
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (mv-nth
           0
           (l6-file-index-list (cdr (assoc-equal name fs))
                               fa-table)))
         (l6-regular-file-length (cdr (assoc-equal name fs))))
        start text))))
    (find-n-free-clusters
     (set-indices-in-fa-table
      fa-table
      (mv-nth 0
              (l6-file-index-list (cdr (assoc-equal name fs))
                                  fa-table))
      (make-list-ac
       (len
        (mv-nth 0
                (l6-file-index-list (cdr (assoc-equal name fs))
                                    fa-table)))
       0 nil))
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (mv-nth
           0
           (l6-file-index-list (cdr (assoc-equal name fs))
                               fa-table)))
         (l6-regular-file-length (cdr (assoc-equal name fs))))
        start text))))))
  :hints
  (("goal"
    :in-theory (disable l6-wrchs-correctness-1-lemma-19)
    :use
    (:instance
     l6-wrchs-correctness-1-lemma-19
     (index-list
      (mv-nth 0
              (l6-file-index-list (cdr (assoc-equal name fs))
                                  fa-table)))))))

(defthm
  l6-wrchs-correctness-1-lemma-22
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
  l6-wrchs-correctness-1-lemma-23
  (lower-bounded-integer-listp
   (find-n-free-clusters fa-table n)
   *ms-first-data-cluster*)
  :hints
  (("goal" :in-theory (enable find-n-free-clusters))))

(defthm
  l6-wrchs-correctness-1-lemma-24
  (implies
   (fat32-masked-entry-p masked-current-cluster)
   (mv-let
     (index-list error-code)
     (l6-build-index-list fa-table masked-current-cluster length)
     (implies
      (and (fat32-masked-entry-p key)
           (< key (len fa-table))
           (not (member-equal key index-list))
           (equal error-code 0))
      (equal
       (l6-build-index-list (update-nth key val fa-table)
                            masked-current-cluster length)
       (l6-build-index-list fa-table
                            masked-current-cluster length)))))
  :hints
  (("goal" :in-theory (enable l6-build-index-list)
    :induct (l6-build-index-list
             fa-table masked-current-cluster length))
   ("subgoal *1/3.2"
    :expand
    (l6-build-index-list (update-nth key val fa-table)
                         masked-current-cluster length))))

(defthm
  l6-wrchs-correctness-1-lemma-25
  (implies
   (and (bounded-nat-listp file-index-list (len fa-table))
        (<= (len fa-table) *ms-bad-cluster*))
   (fat32-masked-entry-list-p file-index-list))
  :hints (("goal" :in-theory (enable fat32-masked-entry-p))))

(defthm
  find-n-free-clusters-correctness-6
  (implies
   (and (fat32-entry-list-p fa-table)
        (>= (len fa-table) *ms-first-data-cluster*)
        (natp n))
   (no-duplicatesp-equal (find-n-free-clusters fa-table n)))
  :hints
  (("goal" :in-theory (disable find-n-free-blocks-correctness-6)
    :use (:instance find-n-free-blocks-correctness-6
                    (alv (fa-table-to-alv fa-table))))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme
       (file-index-list file-length)
     (if
         (or (not (integerp file-length))
             (<= file-length 0))
         file-index-list
       (induction-scheme (cdr file-index-list)
                         (nfix (- file-length *blocksize*)))))
   )

  (defthm
    l6-wrchs-correctness-1-lemma-26
    (implies
     (and (natp file-length)
          (no-duplicatesp-equal file-index-list)
          (feasible-file-length-p (len file-index-list)
                                  file-length)
          (lower-bounded-integer-listp file-index-list *ms-first-data-cluster*)
          (bounded-nat-listp file-index-list (len fa-table))
          (<= (len file-index-list)
              (count-free-blocks (fa-table-to-alv fa-table)))
          (consp file-index-list)
          (fat32-entry-list-p fa-table)
          (<= (len fa-table) *ms-bad-cluster*)
          (<= *ms-first-data-cluster* (len fa-table)))
     (equal
      (l6-build-index-list
       (set-indices-in-fa-table fa-table file-index-list
                                (append (cdr file-index-list)
                                        (list *ms-end-of-clusterchain*)))
       (car file-index-list)
       file-length)
      (mv file-index-list 0)))
    :hints
    (("goal" :in-theory (enable l6-build-index-list
                                set-indices-in-fa-table
                                lower-bounded-integer-listp)
      :induct (induction-scheme file-index-list file-length))
     ("subgoal *1/2.25'" :in-theory (enable feasible-file-length-p))
     ("subgoal *1/2.22'" :in-theory (enable feasible-file-length-p))
     ("subgoal *1/2.19'"
      :in-theory (disable fat32-update-lower-28-correctness-2)
      :use (:instance fat32-update-lower-28-correctness-2
                      (entry (nth (car file-index-list) fa-table))
                      (masked-entry (cadr file-index-list))))
     ("subgoal *1/2.19.2" :in-theory (enable fat32-masked-entry-p))
     ("subgoal *1/2.19.1"
      :expand (set-indices-in-fa-table fa-table file-index-list
                                       (cons (cadr file-index-list)
                                             (append (cddr file-index-list)
                                                     '(268435455))))
      :in-theory (disable set-indices-in-fa-table-correctness-4
                          set-indices-in-fa-table-correctness-3
                          nth-update-nth
                          l6-wrchs-correctness-1-lemma-24
                          l6-wrchs-correctness-1-lemma-25
                          fat32-update-lower-28-correctness-2)
      :use
      ((:instance
        set-indices-in-fa-table-correctness-4
        (key (car file-index-list))
        (val (fat32-update-lower-28 (nth (car file-index-list) fa-table)
                                    (cadr file-index-list)))
        (l fa-table)
        (index-list (cdr file-index-list))
        (value-list (append (cddr file-index-list)
                            '(268435455))))
       (:instance
        set-indices-in-fa-table-correctness-3
        (n (car file-index-list))
        (fa-table (update-nth
            (car file-index-list)
            (fat32-update-lower-28 (nth (car file-index-list) fa-table)
                                   (cadr file-index-list))
            fa-table))
        (index-list (cdr file-index-list))
        (value-list (append (cddr file-index-list)
                            '(268435455))))
       (:instance
        nth-update-nth (m (car file-index-list))
        (n (car file-index-list))
        (val (fat32-update-lower-28 (nth (car file-index-list) fa-table)
                                    (cadr file-index-list)))
        (l fa-table))
       (:instance
        l6-wrchs-correctness-1-lemma-24
        (key (car file-index-list))
        (val (fat32-update-lower-28 (nth (car file-index-list) fa-table)
                                    (cadr file-index-list)))
        (fa-table (set-indices-in-fa-table fa-table (cdr file-index-list)
                                           (append (cddr file-index-list)
                                                   '(268435455))))
        (masked-current-cluster (cadr file-index-list))
        (length (+ -8 file-length)))
       l6-wrchs-correctness-1-lemma-25
       (:instance fat32-update-lower-28-correctness-2
                  (entry (nth (car file-index-list) fa-table))
                  (masked-entry (cadr file-index-list)))))
     ("subgoal *1/1'''" :in-theory (enable feasible-file-length-p)))))

(defthm
  l6-wrchs-correctness-1-lemma-28
  (implies
   (and
    (equal (len disjoint-index-list)
           (len value-list))
    (fat32-masked-entry-list-p value-list)
    (lower-bounded-integer-listp disjoint-index-list
                                 *ms-first-data-cluster*)
    (fat32-masked-entry-list-p disjoint-index-list)
    (<= 2 masked-current-cluster)
    (< masked-current-cluster (len fa-table))
    (fat32-masked-entry-p masked-current-cluster)
    (feasible-file-length-p
     (len
      (mv-nth
       0
       (l6-build-index-list fa-table
                            masked-current-cluster length)))
     length)
    (fat32-entry-list-p fa-table)
    (not
     (intersectp-equal
      disjoint-index-list
      (mv-nth
       0
       (l6-build-index-list fa-table
                            masked-current-cluster length))))
    (equal (mv-nth 1
                   (l6-build-index-list
                    fa-table masked-current-cluster length))
           0))
   (equal (l6-build-index-list
           (set-indices-in-fa-table
            fa-table disjoint-index-list value-list)
           masked-current-cluster length)
          (l6-build-index-list fa-table
                               masked-current-cluster length)))
  :hints (("goal" :in-theory (enable l6-build-index-list
                                     lower-bounded-integer-listp
                                     set-indices-in-fa-table))))

(defthm
  l6-wrchs-correctness-1-lemma-29
  (implies
   (and (l6-fs-p fs)
        (fat32-entry-list-p fa-table)
        (equal (len disjoint-index-list)
               (len value-list))
        (fat32-masked-entry-list-p value-list)
        (lower-bounded-integer-listp disjoint-index-list
                                     *ms-first-data-cluster*)
        (fat32-masked-entry-list-p disjoint-index-list))
   (b*
       (((mv index-list ok)
         (l6-list-all-ok-indices fs fa-table)))
     (implies
      (and ok
           (not (intersectp-equal disjoint-index-list index-list)))
      (equal (l6-to-l4-fs-helper
              fs
              (set-indices-in-fa-table fa-table
                                       disjoint-index-list value-list))
             (l6-to-l4-fs-helper fs fa-table)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (l6-stricter-fs-p fs fa-table)
          (fat32-entry-list-p fa-table)
          (equal (len disjoint-index-list)
                 (len value-list))
          (fat32-masked-entry-list-p value-list)
          (lower-bounded-integer-listp disjoint-index-list
                                       *ms-first-data-cluster*)
          (fat32-masked-entry-list-p disjoint-index-list))
     (b*
         (((mv index-list &)
           (l6-list-all-ok-indices fs fa-table)))
       (implies
        (not (intersectp-equal disjoint-index-list index-list))
        (equal (l6-to-l4-fs-helper
                fs
                (set-indices-in-fa-table fa-table
                                         disjoint-index-list value-list))
               (l6-to-l4-fs-helper fs fa-table)))))))
  :hints (("goal" :in-theory (enable l6-list-all-ok-indices
                                     l6-stricter-fs-p))
          ("subgoal *1/5''" :in-theory (enable l6-file-index-list))))

(defthm
  l6-wrchs-correctness-1-lemma-30
  (implies
   (and
    (fat32-entry-list-p fa-table)
    (l6-fs-p fs)
    (mv-nth 1 (l6-list-all-ok-indices fs fa-table))
    (not (intersectp-equal
          l
          (mv-nth 0
                  (l6-list-all-ok-indices fs fa-table)))))
   (not
    (intersectp-equal
     l
     (mv-nth
      0
      (l6-list-all-ok-indices (delete-assoc-equal name fs)
                              fa-table)))))
  :hints (("goal" :in-theory (enable l6-list-all-ok-indices))))

(defthm
  l6-wrchs-correctness-1-lemma-31
  (implies (l6-stricter-fs-p fs fa-table)
           (l6-stricter-fs-p (delete-assoc-equal name fs)
                             fa-table))
  :hints (("goal" :in-theory (enable l6-stricter-fs-p
                                     l6-list-all-ok-indices))
          ("goal'" :induct t)))

(defthm
  l6-wrchs-correctness-1-lemma-32
  (implies
   (and (fat32-masked-entry-p masked-current-cluster)
        (<= *ms-first-data-cluster*
            masked-current-cluster))
   (lower-bounded-integer-listp
    (mv-nth 0
            (l6-build-index-list
             fa-table masked-current-cluster length))
    *ms-first-data-cluster*))
  :hints
  (("goal" :in-theory (enable l6-build-index-list
                              lower-bounded-integer-listp))))

(defthm
  l6-wrchs-correctness-1-lemma-33
  (implies (and (l6-regular-file-entry-p file))
           (lower-bounded-integer-listp
            (mv-nth 0 (l6-file-index-list file fa-table))
            *ms-first-data-cluster*))
  :hints (("goal" :in-theory (enable l6-file-index-list))))

(defthm
  l6-wrchs-correctness-1-lemma-34
  (implies
   (and
    (l6-regular-file-entry-p file)
    (fat32-entry-list-p fa-table)
    (equal (mv-nth 1 (l6-file-index-list file fa-table))
           0)
    (not (member-equal
          key
          (mv-nth 0 (l6-file-index-list file fa-table))))
    (fat32-masked-entry-p key)
    (< key (len fa-table)))
   (equal
    (l6-file-index-list file (update-nth key val fa-table))
    (l6-file-index-list file fa-table)))
  :hints (("goal" :in-theory (enable l6-file-index-list))))

(defthm
  l6-wrchs-correctness-1-lemma-35
  (implies
   (and
    (l6-fs-p fs)
    (fat32-entry-list-p fa-table)
    (mv-nth 1 (l6-list-all-ok-indices fs fa-table))
    (no-duplicatesp-equal
     (mv-nth 0 (l6-list-all-ok-indices fs fa-table)))
    (not (member-equal
          key
          (mv-nth 0
                  (l6-list-all-ok-indices fs fa-table))))
    (fat32-masked-entry-p key)
    (< key (len fa-table)))
   (equal
    (l6-list-all-ok-indices fs (update-nth key val fa-table))
    (l6-list-all-ok-indices fs fa-table)))
  :hints (("goal" :in-theory (enable l6-list-all-ok-indices))))

(defthm
  l6-wrchs-correctness-1-lemma-36
  (implies
   (and
    (l6-stricter-fs-p fs fa-table)
    (fat32-masked-entry-list-p index-list)
    (fat32-masked-entry-list-p value-list)
    (equal (len index-list)
           (len value-list))
    (not (intersectp-equal
          (mv-nth 0 (l6-list-all-ok-indices fs fa-table))
          index-list)))
   (l6-stricter-fs-p
    fs
    (set-indices-in-fa-table fa-table index-list value-list)))
  :hints
  (("goal"
    :in-theory (enable l6-stricter-fs-p l6-list-all-ok-indices
                       set-indices-in-fa-table))))

(defthm
  l6-wrchs-correctness-1-lemma-37
  (implies
   (and
    (consp (assoc-equal name fs))
    (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
    (l6-fs-p fs)
    (fat32-entry-list-p fa-table)
    (mv-nth 1 (l6-list-all-ok-indices fs fa-table))
    (not (intersectp-equal
          (mv-nth 0 (l6-list-all-ok-indices fs fa-table))
          l)))
   (not
    (intersectp-equal
     l
     (mv-nth 0
             (l6-file-index-list (cdr (assoc-equal name fs))
                                 fa-table)))))
  :hints (("goal" :in-theory (enable l6-list-all-ok-indices))))

(defthm
  l6-wrchs-correctness-1-lemma-38
  (implies
   (and (consp (assoc-equal name fs))
        (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
        (l6-stricter-fs-p fs fa-table))
   (not
    (intersectp-equal
     (mv-nth
      0
      (l6-list-all-ok-indices (delete-assoc-equal name fs)
                              fa-table))
     (mv-nth 0
             (l6-file-index-list (cdr (assoc-equal name fs))
                                 fa-table)))))
  :hints (("goal" :in-theory (enable l6-stricter-fs-p
                                     l6-list-all-ok-indices))))

(defthm
  l6-wrchs-correctness-1-lemma-39
  (implies
   (and
    (equal (l6-regular-file-length (cdr (assoc-equal name fs)))
           0)
    (consp (assoc-equal name fs))
    (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
    (l6-stricter-fs-p fs fa-table))
   (equal
    (len (mv-nth 0
                 (l6-file-index-list (cdr (assoc-equal name fs))
                                     fa-table)))
    0))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (equal
       (l6-regular-file-length (cdr (assoc-equal name fs)))
       0)
      (consp (assoc-equal name fs))
      (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
      (l6-stricter-fs-p fs fa-table))
     (not
      (mv-nth 0
              (l6-file-index-list (cdr (assoc-equal name fs))
                                  fa-table))))
    :hints
    (("goal''"
      :in-theory (e/d (l6-stricter-fs-p)
                      (l6-file-index-list-correctness-1))
      :use (:instance l6-file-index-list-correctness-1
                      (b (len fa-table))
                      (file (cdr (assoc-equal name fs))))
      :expand
      (len
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal name fs))
                                   fa-table)))))))
  :hints
  (("goal"
    :in-theory (enable l6-stricter-fs-p l6-list-all-ok-indices
                       feasible-file-length-p))))

(defthm
  l6-wrchs-correctness-1-lemma-40
  (implies (and (l6-fs-p fs)
                (fat32-entry-list-p fa-table))
           (equal (delete-assoc-equal name
                                      (l6-to-l4-fs-helper fs fa-table))
                  (l6-to-l4-fs-helper (delete-assoc-equal name fs)
                                      fa-table)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (l6-stricter-fs-p fs fa-table)
             (equal (delete-assoc-equal name
                                        (l6-to-l4-fs-helper fs fa-table))
                    (l6-to-l4-fs-helper (delete-assoc-equal name fs)
                                        fa-table)))
    :hints (("goal" :in-theory (enable l6-stricter-fs-p))))))

(defthm
  l6-wrchs-correctness-1-lemma-41
  (implies
   (and
    (consp (assoc-equal name fs))
    (not (l6-regular-file-entry-p (cdr (assoc-equal name fs))))
    (l6-fs-p fs)
    (fat32-entry-list-p fa-table)
    (not (intersectp-equal
          l
          (mv-nth 0
                  (l6-list-all-ok-indices fs fa-table)))))
   (not
    (intersectp-equal
     l
     (mv-nth 0
             (l6-list-all-ok-indices (cdr (assoc-equal name fs))
                                     fa-table)))))
  :hints (("goal" :in-theory (enable l6-list-all-ok-indices))))

(defthm
  l6-wrchs-correctness-1-lemma-42
  (implies
   (and
    (l6-regular-file-entry-p file)
    (fat32-entry-list-p fa-table)
    (equal (len disjoint-index-list)
           (len value-list))
    (fat32-masked-entry-list-p value-list)
    (lower-bounded-integer-listp disjoint-index-list
                                 *ms-first-data-cluster*)
    (fat32-masked-entry-list-p disjoint-index-list)
    (feasible-file-length-p
     (len (mv-nth 0 (l6-file-index-list file fa-table)))
     (l6-regular-file-length file))
    (not (intersectp-equal
          disjoint-index-list
          (mv-nth 0 (l6-file-index-list file fa-table))))
    (equal (mv-nth 1 (l6-file-index-list file fa-table))
           0))
   (equal
    (l6-file-index-list
     file
     (set-indices-in-fa-table fa-table
                              disjoint-index-list value-list))
    (l6-file-index-list file fa-table)))
  :hints (("goal" :in-theory (enable l6-file-index-list))))

(defthm
  l6-wrchs-correctness-1-lemma-43
  (implies
   (and (l6-fs-p fs)
        (fat32-entry-list-p fa-table)
        (equal (len disjoint-index-list)
               (len value-list))
        (fat32-masked-entry-list-p value-list)
        (lower-bounded-integer-listp disjoint-index-list
                                     *ms-first-data-cluster*)
        (fat32-masked-entry-list-p disjoint-index-list))
   (b*
       (((mv index-list ok)
         (l6-list-all-ok-indices fs fa-table)))
     (implies
      (and
       ok
       (not (intersectp-equal disjoint-index-list index-list)))
      (equal
       (l6-list-all-ok-indices
        fs
        (set-indices-in-fa-table fa-table
                                 disjoint-index-list value-list))
       (l6-list-all-ok-indices fs fa-table)))))
  :hints
  (("goal" :in-theory (enable l6-list-all-ok-indices
                              l6-stricter-fs-p))
   ("subgoal *1/5''" :in-theory (enable l6-file-index-list))))

(defthm
  l6-wrchs-correctness-1-lemma-44
  (implies
   (and (l6-fs-p fs)
        (fat32-entry-list-p fa-table)
        (<= *ms-first-data-cluster* (len fa-table))
        (mv-nth 1 (l6-list-all-ok-indices fs fa-table))
        (natp n))
   (not (intersectp-equal
         (mv-nth 0 (l6-list-all-ok-indices fs fa-table))
         (find-n-free-clusters fa-table n))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable l4-wrchs-returns-stricter-fs-lemma-15
                        l6-list-all-ok-indices-correctness-5
                        l6-stricter-fs-p-correctness-1-lemma-3)
    :use
    ((:instance
      l4-wrchs-returns-stricter-fs-lemma-15
      (alv (fa-table-to-alv fa-table))
      (l (mv-nth 0
                 (l6-list-all-ok-indices fs fa-table))))
     l6-list-all-ok-indices-correctness-5
     l6-stricter-fs-p-correctness-1-lemma-3))))

(defthmd
  l6-wrchs-correctness-1-lemma-45
  (implies
   (and
    (consp hns)
    (consp fs2)
    (consp (assoc-equal (car hns) fs2))
    (l6-regular-file-entry-p (cdr (assoc-equal (car hns) fs2)))
    (not (cdr hns))
    (l6-fs-p fs2)
    (fat32-entry-list-p fa-table)
    (mv-nth 1 (l6-list-all-ok-indices fs2 fa-table))
    (no-duplicatesp-equal (mv-nth 0
                                  (l6-list-all-ok-indices fs2 fa-table)))
    (l6-fs-p fs1)
    (mv-nth 1 (l6-list-all-ok-indices fs1 fa-table))
    (no-duplicatesp-equal (mv-nth 0
                                  (l6-list-all-ok-indices fs1 fa-table)))
    (stringp text)
    (integerp start)
    (<= 0 start)
    (symbolp (car hns))
    (block-listp disk)
    (equal (len disk) (len fa-table))
    (<= (len disk) *ms-bad-cluster*)
    (<= *ms-first-data-cluster* (len disk))
    (<= (len (make-blocks (insert-text nil start text)))
        (count-free-blocks (fa-table-to-alv fa-table)))
    (not (intersectp-equal (mv-nth 0 (l6-list-all-ok-indices fs1 fa-table))
                           (mv-nth 0
                                   (l6-list-all-ok-indices fs2 fa-table))))
    (consp
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                                   fa-table))
       (make-list-ac
        (len (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                                         fa-table)))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth 0
                   (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                                       fa-table)))
          (l6-regular-file-length (cdr (assoc-equal (car hns) fs2))))
         start text))))))
   (equal
    (l6-to-l4-fs-helper fs1 fa-table)
    (l6-to-l4-fs-helper
     fs1
     (set-indices-in-fa-table
      (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                                   fa-table))
       (make-list-ac
        (len (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                                         fa-table)))
        0 nil))
      (find-n-free-clusters
       (set-indices-in-fa-table
        fa-table
        (mv-nth 0
                (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                                    fa-table))
        (make-list-ac
         (len (mv-nth 0
                      (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                                          fa-table)))
         0 nil))
       (len
        (make-blocks
         (insert-text
          (unmake-blocks
           (fetch-blocks-by-indices
            disk
            (mv-nth 0
                    (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                                        fa-table)))
           (l6-regular-file-length (cdr (assoc-equal (car hns) fs2))))
          start text))))
      (append
       (cdr
        (find-n-free-clusters
         (set-indices-in-fa-table
          fa-table
          (mv-nth 0
                  (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                                      fa-table))
          (make-list-ac
           (len (mv-nth 0
                        (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                                            fa-table)))
           0 nil))
         (len
          (make-blocks
           (insert-text
            (unmake-blocks
             (fetch-blocks-by-indices
              disk
              (mv-nth 0
                      (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                                          fa-table)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs2))))
            start text)))))
       (list *ms-end-of-clusterchain*))))))
  :instructions
  (:promote (:dive 2)
            (:rewrite (:rewrite l6-wrchs-correctness-1-lemma-29 . 1))
            (:change-goal nil t)
            :bash (:change-goal nil t)
            :bash :bash :bash :bash (:dive 1)
            (:rewrite intersectp-is-commutative)
            (:rewrite l6-wrchs-correctness-1-lemma-44)
            :bash :bash :bash
            (:rewrite (:rewrite l6-wrchs-correctness-1-lemma-29 . 1))
            :top :bash
            :bash :bash :bash :bash :bash (:dive 2)
            (:rewrite len-of-binary-append)
            :top (:dive 1)
            (:rewrite len)
            :top :bash))

(defthm
  l6-wrchs-correctness-1-lemma-46
  (implies
   (and
    (l6-stricter-fs-p fs2 fa-table)
    (l6-stricter-fs-p fs1 fa-table)
    (not (intersectp-equal
          (mv-nth 0 (l6-list-all-ok-indices fs1 fa-table))
          (mv-nth 0
                  (l6-list-all-ok-indices fs2 fa-table))))
    (fat32-entry-list-p fa-table)
    (stringp text)
    (integerp start)
    (<= 0 start)
    (symbol-listp hns)
    (block-listp disk)
    (equal (len disk) (len fa-table))
    (<= (len disk) *ms-bad-cluster*)
    (<= *ms-first-data-cluster* (len disk))
    (<= (len (make-blocks (insert-text nil start text)))
        (count-free-blocks (fa-table-to-alv fa-table))))
   (equal
    (l6-to-l4-fs-helper
     fs1
     (mv-nth 2
             (l6-wrchs hns fs2 disk fa-table start text)))
    (l6-to-l4-fs-helper fs1 fa-table)))
  :hints
  (("goal" :in-theory (enable l6-stricter-fs-p
                              l6-wrchs-correctness-1-lemma-45))
   ("subgoal *1/6.8'"
    :in-theory (disable l6-wrchs-correctness-1-lemma-29
                        intersectp-is-commutative)
    :use
    ((:instance
      intersectp-is-commutative
      (x (mv-nth 0
                 (l6-list-all-ok-indices fs1 fa-table)))
      (y
       (find-n-free-clusters
        (set-indices-in-fa-table
         fa-table
         (mv-nth
          0
          (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                              fa-table))
         (make-list-ac
          (len (mv-nth 0
                       (l6-file-index-list
                        (cdr (assoc-equal (car hns) fs2))
                        fa-table)))
          0 nil))
        (len
         (make-blocks
          (insert-text
           (unmake-blocks
            (fetch-blocks-by-indices
             disk
             (mv-nth 0
                     (l6-file-index-list
                      (cdr (assoc-equal (car hns) fs2))
                      fa-table)))
            (l6-regular-file-length
             (cdr (assoc-equal (car hns) fs2))))
           start text))))))
     (:instance
      l6-wrchs-correctness-1-lemma-29 (fs fs1)
      (fa-table
       (set-indices-in-fa-table
        fa-table
        (mv-nth
         0
         (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                             fa-table))
        (make-list-ac
         (len
          (mv-nth
           0
           (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                               fa-table)))
         0 nil)))
      (disjoint-index-list
       (find-n-free-clusters
        (set-indices-in-fa-table
         fa-table
         (mv-nth
          0
          (l6-file-index-list (cdr (assoc-equal (car hns) fs2))
                              fa-table))
         (make-list-ac
          (len (mv-nth 0
                       (l6-file-index-list
                        (cdr (assoc-equal (car hns) fs2))
                        fa-table)))
          0 nil))
        (len
         (make-blocks
          (insert-text
           (unmake-blocks
            (fetch-blocks-by-indices
             disk
             (mv-nth 0
                     (l6-file-index-list
                      (cdr (assoc-equal (car hns) fs2))
                      fa-table)))
            (l6-regular-file-length
             (cdr (assoc-equal (car hns) fs2))))
           start text)))))
      (value-list
       (append
        (cdr
         (find-n-free-clusters
          (set-indices-in-fa-table
           fa-table
           (mv-nth 0
                   (l6-file-index-list
                    (cdr (assoc-equal (car hns) fs2))
                    fa-table))
           (make-list-ac
            (len (mv-nth 0
                         (l6-file-index-list
                          (cdr (assoc-equal (car hns) fs2))
                          fa-table)))
            0 nil))
          (len
           (make-blocks
            (insert-text
             (unmake-blocks
              (fetch-blocks-by-indices
               disk
               (mv-nth 0
                       (l6-file-index-list
                        (cdr (assoc-equal (car hns) fs2))
                        fa-table)))
              (l6-regular-file-length
               (cdr (assoc-equal (car hns) fs2))))
             start text)))))
        '(268435455))))))))

(defthm
  l6-wrchs-correctness-1-lemma-47
  (implies
   (and (consp (assoc-equal name fs))
        (l6-fs-p (cdr (assoc-equal name fs)))
        (l6-fs-p fs)
        (fat32-entry-list-p fa-table)
        (no-duplicatesp-equal (mv-nth 0
                                      (l6-list-all-ok-indices fs fa-table))))
   (not (intersectp-equal
         (mv-nth 0
                 (l6-list-all-ok-indices (delete-assoc-equal name fs)
                                         fa-table))
         (mv-nth 0
                 (l6-list-all-ok-indices (cdr (assoc-equal name fs))
                                         fa-table)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (consp (assoc-equal name fs))
          (l6-fs-p (cdr (assoc-equal name fs)))
          (l6-stricter-fs-p fs fa-table)
          (fat32-entry-list-p fa-table))
     (not (intersectp-equal
           (mv-nth 0
                   (l6-list-all-ok-indices (delete-assoc-equal name fs)
                                           fa-table))
           (mv-nth 0
                   (l6-list-all-ok-indices (cdr (assoc-equal name fs))
                                           fa-table)))))
    :hints (("goal" :in-theory (enable l6-stricter-fs-p)))))
  :hints (("goal" :in-theory (enable l6-list-all-ok-indices))))

(defthm l6-wrchs-correctness-1-lemma-1
  (implies
   (and
    (consp hns)
    (consp fs)
    (consp (assoc-equal (car hns) fs))
    (not (l6-regular-file-entry-p (cdr (assoc-equal (car hns) fs))))
    (equal
     (l4-wrchs (cdr hns)
               (l6-to-l4-fs-helper (cdr (assoc-equal (car hns) fs))
                                   fa-table)
               disk (fa-table-to-alv fa-table)
               start text)
     (list
      (l6-to-l4-fs-helper (mv-nth 0
                                  (l6-wrchs (cdr hns)
                                            (cdr (assoc-equal (car hns) fs))
                                            disk fa-table start text))
                          (mv-nth 2
                                  (l6-wrchs (cdr hns)
                                            (cdr (assoc-equal (car hns) fs))
                                            disk fa-table start text)))
      (mv-nth 1
              (l6-wrchs (cdr hns)
                        (cdr (assoc-equal (car hns) fs))
                        disk fa-table start text))
      (fa-table-to-alv (mv-nth 2
                               (l6-wrchs (cdr hns)
                                         (cdr (assoc-equal (car hns) fs))
                                         disk fa-table start text)))))
    (l6-stricter-fs-p fs fa-table)
    (fat32-entry-list-p fa-table)
    (stringp text)
    (integerp start)
    (<= 0 start)
    (symbol-listp hns)
    (block-listp disk)
    (equal (len disk) (len fa-table))
    (<= (len fa-table) *ms-bad-cluster*)
    (<= 2 (len fa-table))
    (<= (len (make-blocks (insert-text nil start text)))
        (count-free-blocks (fa-table-to-alv fa-table))))
   (equal
    (l4-wrchs hns (l6-to-l4-fs-helper fs fa-table)
              disk (fa-table-to-alv fa-table)
              start text)
    (list
     (l6-to-l4-fs-helper (mv-nth 0
                                 (l6-wrchs hns fs disk fa-table start text))
                         (mv-nth 2
                                 (l6-wrchs hns fs disk fa-table start text)))
     (mv-nth 1
             (l6-wrchs hns fs disk fa-table start text))
     (fa-table-to-alv (mv-nth 2
                              (l6-wrchs hns fs disk fa-table start text)))))))

(defthm
  l6-wrchs-correctness-1-lemma-27
  (implies
   (and
    (consp hns)
    (consp fs)
    (consp (assoc-equal (car hns) fs))
    (l6-regular-file-entry-p (cdr (assoc-equal (car hns) fs)))
    (not (cdr hns))
    (<=
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (mv-nth 0
                  (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                      fa-table)))
         (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
        start text)))
     (+ (count-free-blocks (fa-table-to-alv fa-table))
        (len (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                         fa-table)))))
    (consp
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                   fa-table))
       (make-list-ac
        (len (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                         fa-table)))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth 0
                   (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                       fa-table)))
          (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
         start text)))))
    (l6-stricter-fs-p fs fa-table)
    (stringp text)
    (integerp start)
    (<= 0 start)
    (symbolp (car hns))
    (block-listp disk)
    (equal (len disk) (len fa-table))
    (<= (len disk) 268435447)
    (<= 2 (len disk))
    (<= (len (make-blocks (insert-text nil start text)))
        (count-free-blocks (fa-table-to-alv fa-table))))
   (equal
    (len
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                   fa-table))
       (make-list-ac
        (len (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                         fa-table)))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth 0
                   (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                       fa-table)))
          (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
         start text)))))
    (len
     (append
      (cdr
       (find-n-free-clusters
        (set-indices-in-fa-table
         fa-table
         (mv-nth 0
                 (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                     fa-table))
         (make-list-ac
          (len (mv-nth 0
                       (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                           fa-table)))
          0 nil))
        (len
         (make-blocks
          (insert-text
           (unmake-blocks
            (fetch-blocks-by-indices
             disk
             (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                         fa-table)))
            (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
           start text)))))
      '(268435455)))))
  :hints
  (("goal"
    :in-theory (disable l6-wrchs-correctness-1-lemma-7
                        l6-wrchs-correctness-1-lemma-20)
    :expand
    (len
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                   fa-table))
       (make-list-ac
        (len (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                         fa-table)))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth 0
                   (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                       fa-table)))
          (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
         start text))))))))

(defthm
  l6-wrchs-correctness-1-lemma-54
  (implies
   (and
    (consp hns)
    (consp fs)
    (consp (assoc-equal (car hns) fs))
    (l6-regular-file-entry-p (cdr (assoc-equal (car hns) fs)))
    (not (cdr hns))
    (<=
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (mv-nth 0
                  (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                      fa-table)))
         (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
        start text)))
     (+ (count-free-blocks (fa-table-to-alv fa-table))
        (len (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                         fa-table)))))
    (consp
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                   fa-table))
       (make-list-ac
        (len (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                         fa-table)))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth 0
                   (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                       fa-table)))
          (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
         start text)))))
    (l6-stricter-fs-p fs fa-table)
    (stringp text)
    (integerp start)
    (<= 0 start)
    (symbolp (car hns))
    (block-listp disk)
    (equal (len disk) (len fa-table))
    (<= (len disk) 268435447)
    (<= 2 (len disk))
    (<= (len (make-blocks (insert-text nil start text)))
        (count-free-blocks (fa-table-to-alv fa-table)))
    (equal
     (+
      1
      (len
       (cdr
        (find-n-free-clusters
         (set-indices-in-fa-table
          fa-table
          (mv-nth 0
                  (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                      fa-table))
          (make-list-ac
           (len (mv-nth 0
                        (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                            fa-table)))
           0 nil))
         (len
          (make-blocks
           (insert-text
            (unmake-blocks
             (fetch-blocks-by-indices
              disk
              (mv-nth 0
                      (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                          fa-table)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
            start text)))))))
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (mv-nth 0
                  (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                      fa-table)))
         (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
        start text)))))
   (not
    (intersectp-equal
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                   fa-table))
       (make-list-ac
        (len (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                         fa-table)))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth 0
                   (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                       fa-table)))
          (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
         start text))))
     (mv-nth
      0
      (l6-list-all-ok-indices
       (delete-assoc-equal (car hns) fs)
       (set-indices-in-fa-table
        fa-table
        (mv-nth 0
                (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                    fa-table))
        (make-list-ac
         (len (mv-nth 0
                      (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                          fa-table)))
         0 nil)))))))
  :instructions (:promote (:dive 1)
                          (:rewrite intersectp-is-commutative)
                          (:rewrite l6-wrchs-correctness-1-lemma-44)
                          :bash :bash
                          :bash :bash))

(defthm
  l6-wrchs-correctness-1-lemma-55
  (implies
   (and
    (consp hns)
    (consp fs)
    (consp (assoc-equal (car hns) fs))
    (l6-regular-file-entry-p (cdr (assoc-equal (car hns) fs)))
    (not (cdr hns))
    (<=
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (mv-nth
           0
           (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                               fa-table)))
         (l6-regular-file-length
          (cdr (assoc-equal (car hns) fs))))
        start text)))
     (+
      (count-free-blocks (fa-table-to-alv fa-table))
      (len
       (mv-nth
        0
        (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                            fa-table)))))
    (consp
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth
        0
        (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                            fa-table))
       (make-list-ac
        (len
         (mv-nth
          0
          (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                              fa-table)))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth
            0
            (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                fa-table)))
          (l6-regular-file-length
           (cdr (assoc-equal (car hns) fs))))
         start text)))))
    (l6-stricter-fs-p fs fa-table)
    (stringp text)
    (integerp start)
    (<= 0 start)
    (symbolp (car hns))
    (block-listp disk)
    (equal (len disk) (len fa-table))
    (<= (len disk) 268435447)
    (<= 2 (len disk))
    (<= (len (make-blocks (insert-text nil start text)))
        (count-free-blocks (fa-table-to-alv fa-table)))
    (equal
     (+
      1
      (len
       (cdr
        (find-n-free-clusters
         (set-indices-in-fa-table
          fa-table
          (mv-nth
           0
           (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                               fa-table))
          (make-list-ac
           (len (mv-nth 0
                        (l6-file-index-list
                         (cdr (assoc-equal (car hns) fs))
                         fa-table)))
           0 nil))
         (len
          (make-blocks
           (insert-text
            (unmake-blocks
             (fetch-blocks-by-indices
              disk
              (mv-nth 0
                      (l6-file-index-list
                       (cdr (assoc-equal (car hns) fs))
                       fa-table)))
             (l6-regular-file-length
              (cdr (assoc-equal (car hns) fs))))
            start text)))))))
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (mv-nth
           0
           (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                               fa-table)))
         (l6-regular-file-length
          (cdr (assoc-equal (car hns) fs))))
        start text)))))
   (lower-bounded-integer-listp
    (cdr
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth
        0
        (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                            fa-table))
       (make-list-ac
        (len
         (mv-nth
          0
          (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                              fa-table)))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth
            0
            (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                fa-table)))
          (l6-regular-file-length
           (cdr (assoc-equal (car hns) fs))))
         start text)))))
    *ms-first-data-cluster*))
  :hints
  (("goal"
    :use
    (:instance
     lower-bounded-integer-listp
     (l
      (find-n-free-clusters
       (set-indices-in-fa-table
        fa-table
        (mv-nth
         0
         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                             fa-table))
        (make-list-ac
         (len
          (mv-nth
           0
           (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                               fa-table)))
         0 nil))
       (len
        (make-blocks
         (insert-text
          (unmake-blocks
           (fetch-blocks-by-indices
            disk
            (mv-nth 0
                    (l6-file-index-list
                     (cdr (assoc-equal (car hns) fs))
                     fa-table)))
           (l6-regular-file-length
            (cdr (assoc-equal (car hns) fs))))
          start text)))))
     (b *ms-first-data-cluster*)))))

(defthm
  l6-wrchs-correctness-1-lemma-56
  (implies
   (and
    (consp hns)
    (consp fs)
    (consp (assoc-equal (car hns) fs))
    (l6-regular-file-entry-p (cdr (assoc-equal (car hns) fs)))
    (not (cdr hns))
    (<=
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (mv-nth 0
                  (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                      fa-table)))
         (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
        start text)))
     (+ (count-free-blocks (fa-table-to-alv fa-table))
        (len (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                         fa-table)))))
    (consp
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                   fa-table))
       (make-list-ac
        (len (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                         fa-table)))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth 0
                   (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                       fa-table)))
          (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
         start text)))))
    (l6-stricter-fs-p fs fa-table)
    (stringp text)
    (integerp start)
    (<= 0 start)
    (symbolp (car hns))
    (block-listp disk)
    (equal (len disk) (len fa-table))
    (<= (len disk) 268435447)
    (<= 2 (len disk))
    (<= (len (make-blocks (insert-text nil start text)))
        (count-free-blocks (fa-table-to-alv fa-table)))
    (equal
     (+
      1
      (len
       (cdr
        (find-n-free-clusters
         (set-indices-in-fa-table
          fa-table
          (mv-nth 0
                  (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                      fa-table))
          (make-list-ac
           (len (mv-nth 0
                        (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                            fa-table)))
           0 nil))
         (len
          (make-blocks
           (insert-text
            (unmake-blocks
             (fetch-blocks-by-indices
              disk
              (mv-nth 0
                      (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                          fa-table)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
            start text)))))))
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (mv-nth 0
                  (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                      fa-table)))
         (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
        start text)))))
   (not
    (intersectp-equal
     (mv-nth 0
             (l6-list-all-ok-indices (delete-assoc-equal (car hns) fs)
                                     fa-table))
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                   fa-table))
       (make-list-ac
        (len (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                         fa-table)))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth 0
                   (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                       fa-table)))
          (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
         start text)))))))
  :hints
  (("goal"
    :in-theory (disable l6-wrchs-correctness-1-lemma-44
                        l6-wrchs-correctness-1-lemma-43)
    :use
    ((:instance
      l6-wrchs-correctness-1-lemma-43
      (fs (delete-assoc-equal (car hns) fs))
      (disjoint-index-list
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                   fa-table)))
      (value-list
       (make-list-ac
        (len (mv-nth 0
                     (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                         fa-table)))
        0 nil)))
     (:instance
      l6-wrchs-correctness-1-lemma-44
      (fs (delete-assoc-equal (car hns) fs))
      (fa-table
       (set-indices-in-fa-table
        fa-table
        (mv-nth 0
                (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                    fa-table))
        (make-list-ac
         (len (mv-nth 0
                      (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                          fa-table)))
         0 nil)))
      (n
       (len
        (make-blocks
         (insert-text
          (unmake-blocks
           (fetch-blocks-by-indices
            disk
            (mv-nth 0
                    (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                        fa-table)))
           (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
          start text)))))))))

(defthm
  l6-wrchs-correctness-1-lemma-57
  (implies
   (and (consp (assoc-equal name fs))
        (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
        (l6-stricter-fs-p fs fa-table))
   (iff
    (consp
     (mv-nth 0
             (l6-file-index-list (cdr (assoc-equal name fs))
                                 fa-table)))
    (not
     (equal (l6-regular-file-length (cdr (assoc-equal name fs)))
            0))))
  :hints
  (("goal"
    :in-theory (enable l6-stricter-fs-p l6-list-all-ok-indices
                       feasible-file-length-p))))

(defthm
  l6-wrchs-correctness-1-lemma-59
  (implies
   (and (consp (assoc-equal name fs))
        (l6-regular-file-entry-p (cdr (assoc-equal name fs)))
        (l6-stricter-fs-p fs fa-table))
   (equal
    (mv-nth 1
            (l6-file-index-list (cdr (assoc-equal name fs))
                                fa-table))
    0))
  :hints (("goal" :in-theory (enable l6-stricter-fs-p
                                     l6-list-all-ok-indices))))

(defthm
 l6-wrchs-correctness-1-lemma-58
 (implies
  (and
   (consp hns)
   (consp fs)
   (consp (assoc-equal (car hns) fs))
   (l6-regular-file-entry-p (cdr (assoc-equal (car hns) fs)))
   (not (cdr hns))
   (<=
    (len
     (make-blocks
      (insert-text
       (unmake-blocks
            (fetch-blocks-by-indices
                 disk
                 (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
       start text)))
    (+ (count-free-blocks (fa-table-to-alv fa-table))
       (len (mv-nth 0
                    (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                        fa-table)))))
   (consp
    (find-n-free-clusters
     (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                   fa-table))
       (make-list-ac
            (len (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            0 nil))
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
            (fetch-blocks-by-indices
                 disk
                 (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
        start text)))))
   (l6-stricter-fs-p fs fa-table)
   (stringp text)
   (integerp start)
   (<= 0 start)
   (symbolp (car hns))
   (block-listp disk)
   (equal (len disk) (len fa-table))
   (<= (len disk) 268435447)
   (<= 2 (len disk))
   (<= (len (make-blocks (insert-text nil start text)))
       (count-free-blocks (fa-table-to-alv fa-table)))
   (equal
    (+
     1
     (len
      (cdr
       (find-n-free-clusters
        (set-indices-in-fa-table
         fa-table
         (mv-nth 0
                 (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                     fa-table))
         (make-list-ac
            (len (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            0 nil))
        (len
         (make-blocks
          (insert-text
           (unmake-blocks
            (fetch-blocks-by-indices
                 disk
                 (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
           start text)))))))
    (len
     (make-blocks
      (insert-text
       (unmake-blocks
            (fetch-blocks-by-indices
                 disk
                 (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
       start text)))))
  (equal
   (mv-nth
    0
    (l6-file-index-list
     (l6-make-regular-file
      (car
       (find-n-free-clusters
        (set-indices-in-fa-table
         fa-table
         (mv-nth 0
                 (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                     fa-table))
         (make-list-ac
            (len (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            0 nil))
        (len
         (make-blocks
          (insert-text
           (unmake-blocks
            (fetch-blocks-by-indices
                 disk
                 (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
           start text)))))
      (len
       (insert-text
        (unmake-blocks
            (fetch-blocks-by-indices
                 disk
                 (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
        start text)))
     (set-indices-in-fa-table
      (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                   fa-table))
       (make-list-ac
            (len (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            0 nil))
      (find-n-free-clusters
       (set-indices-in-fa-table
        fa-table
        (mv-nth 0
                (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                    fa-table))
        (make-list-ac
            (len (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            0 nil))
       (len
        (make-blocks
         (insert-text
          (unmake-blocks
            (fetch-blocks-by-indices
                 disk
                 (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
          start text))))
      (append
       (cdr
        (find-n-free-clusters
         (set-indices-in-fa-table
          fa-table
          (mv-nth 0
                  (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                      fa-table))
          (make-list-ac
            (len (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            0 nil))
         (len
          (make-blocks
           (insert-text
            (unmake-blocks
             (fetch-blocks-by-indices
                 disk
                 (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
            start text)))))
       '(268435455)))))
   (find-n-free-clusters
    (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                   fa-table))
       (make-list-ac
            (len (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            0 nil))
    (len
     (make-blocks
      (insert-text
       (unmake-blocks
            (fetch-blocks-by-indices
                 disk
                 (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
       start text))))))
 :instructions
 ((:in-theory
   (e/d
       (l6-file-index-list lower-bounded-integer-listp)
       (l6-wrchs-correctness-1-lemma-23 find-n-free-clusters-correctness-1)))
  (:use
   (:instance
    l6-wrchs-correctness-1-lemma-23
    (fa-table
     (set-indices-in-fa-table
       fa-table
       (mv-nth 0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                   fa-table))
       (make-list-ac
            (len (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            0 nil)))
    (n
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
            (fetch-blocks-by-indices
                 disk
                 (mv-nth 0
                         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                             fa-table)))
            (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
        start text)))))
   (:instance find-n-free-clusters-correctness-1
              (b (len disk))
              (fa-table (set-indices-in-fa-table fa-table nil nil))
              (n (len (make-blocks (insert-text nil start text)))))
   (:instance
    find-n-free-clusters-correctness-1
    (b (len disk))
    (fa-table
     (set-indices-in-fa-table
      fa-table
      (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
      (make-list-ac
       (len
        (mv-nth
         0
         (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
       0 nil)))
    (n
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (mv-nth
           0
           (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
         (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
        start text))))))
  :bash (:dive 1 2)
  (:claim
   (and
    (no-duplicatesp-equal
     (find-n-free-clusters (set-indices-in-fa-table fa-table nil nil)
                           (len (make-blocks (insert-text nil start text)))))
    (feasible-file-length-p
         (len (find-n-free-clusters
                   (set-indices-in-fa-table fa-table nil nil)
                   (len (make-blocks (insert-text nil start text)))))
         (len (insert-text nil start text)))
    (lower-bounded-integer-listp
      (find-n-free-clusters (set-indices-in-fa-table fa-table nil nil)
                            (len (make-blocks (insert-text nil start text))))
      2)
    (bounded-nat-listp
      (find-n-free-clusters (set-indices-in-fa-table fa-table nil nil)
                            (len (make-blocks (insert-text nil start text))))
      (len (set-indices-in-fa-table fa-table nil nil)))
    (<= (len (find-n-free-clusters
                  (set-indices-in-fa-table fa-table nil nil)
                  (len (make-blocks (insert-text nil start text)))))
        (count-free-blocks
             (fa-table-to-alv (set-indices-in-fa-table fa-table nil nil))))
    (fat32-entry-list-p (set-indices-in-fa-table fa-table nil nil))
    (<= (len (set-indices-in-fa-table fa-table nil nil))
        268435447)
    (<= 2
        (len (set-indices-in-fa-table fa-table nil nil))))
   :hints :none)
  (:rewrite l6-wrchs-correctness-1-lemma-26)
  :top :bash :bash
  (:use (:instance find-n-free-clusters-correctness-2
                   (fa-table (set-indices-in-fa-table fa-table nil nil))
                   (n (len (make-blocks (insert-text nil start text))))))
  :promote (:demote 1)
  (:dive 1)
  :x :top :s
  (:bash ("goal" :in-theory (enable set-indices-in-alv)))
  (:dive 1 2)
  (:claim
   (and
    (no-duplicatesp-equal
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
       (make-list-ac
        (len
         (mv-nth
          0
          (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth
            0
            (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
          (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
         start text)))))
    (feasible-file-length-p
     (len
      (find-n-free-clusters
       (set-indices-in-fa-table
        fa-table
        (mv-nth
         0
         (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
        (make-list-ac
         (len
          (mv-nth
           0
           (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
         0 nil))
       (len
        (make-blocks
         (insert-text
          (unmake-blocks
           (fetch-blocks-by-indices
            disk
            (mv-nth
             0
             (l6-build-index-list
                 fa-table
                 (l6-regular-file-first-cluster
                      (cdr (assoc-equal (car hns) fs)))
                 (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
           (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
          start text)))))
     (len
      (insert-text
       (unmake-blocks
        (fetch-blocks-by-indices
         disk
         (mv-nth
          0
          (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
        (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
       start text)))
    (lower-bounded-integer-listp
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
       (make-list-ac
        (len
         (mv-nth
          0
          (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth
            0
            (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
          (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
         start text))))
     2)
    (bounded-nat-listp
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
       (make-list-ac
        (len
         (mv-nth
          0
          (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks
          (fetch-blocks-by-indices
           disk
           (mv-nth
            0
            (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
          (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
         start text))))
     (len
      (set-indices-in-fa-table
       fa-table
       (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
       (make-list-ac
        (len
         (mv-nth
          0
          (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
        0 nil))))
    (<=
     (len
      (find-n-free-clusters
       (set-indices-in-fa-table
        fa-table
        (mv-nth
         0
         (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
        (make-list-ac
         (len
          (mv-nth
           0
           (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
         0 nil))
       (len
        (make-blocks
         (insert-text
          (unmake-blocks
           (fetch-blocks-by-indices
            disk
            (mv-nth
             0
             (l6-build-index-list
                 fa-table
                 (l6-regular-file-first-cluster
                      (cdr (assoc-equal (car hns) fs)))
                 (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
           (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
          start text)))))
     (count-free-blocks
      (fa-table-to-alv
       (set-indices-in-fa-table
        fa-table
        (mv-nth
         0
         (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
        (make-list-ac
         (len
          (mv-nth
           0
           (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
         0 nil)))))
    (fat32-entry-list-p
     (set-indices-in-fa-table
      fa-table
      (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
      (make-list-ac
       (len
        (mv-nth
         0
         (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
       0 nil)))
    (<=
     (len
      (set-indices-in-fa-table
       fa-table
       (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
       (make-list-ac
        (len
         (mv-nth
          0
          (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
        0 nil)))
     268435447)
    (<=
     2
     (len
      (set-indices-in-fa-table
       fa-table
       (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
       (make-list-ac
        (len
         (mv-nth
          0
          (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
        0 nil)))))
   :hints :none)
  (:rewrite l6-wrchs-correctness-1-lemma-26)
  :top :bash :bash
  (:use
   (:instance
    find-n-free-clusters-correctness-2
    (fa-table
     (set-indices-in-fa-table
      fa-table
      (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
      (make-list-ac
       (len
        (mv-nth
         0
         (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
       0 nil)))
    (n
     (len
      (make-blocks
       (insert-text
        (unmake-blocks
         (fetch-blocks-by-indices
          disk
          (mv-nth
           0
           (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
         (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
        start text))))))
  :promote (:demote 1)
  (:dive 1)
  :x :up :s (:change-goal nil t)
  (:change-goal nil t)
  (:dive 1 2)
  (:claim
   (and
    (no-duplicatesp-equal
     (find-n-free-clusters (set-indices-in-fa-table fa-table nil nil)
                           (len (make-blocks (insert-text nil start text)))))
    (feasible-file-length-p
         (len (find-n-free-clusters
                   (set-indices-in-fa-table fa-table nil nil)
                   (len (make-blocks (insert-text nil start text)))))
         (len (insert-text nil start text)))
    (lower-bounded-integer-listp
      (find-n-free-clusters (set-indices-in-fa-table fa-table nil nil)
                            (len (make-blocks (insert-text nil start text))))
      2)
    (bounded-nat-listp
      (find-n-free-clusters (set-indices-in-fa-table fa-table nil nil)
                            (len (make-blocks (insert-text nil start text))))
      (len (set-indices-in-fa-table fa-table nil nil)))
    (<= (len (find-n-free-clusters
                  (set-indices-in-fa-table fa-table nil nil)
                  (len (make-blocks (insert-text nil start text)))))
        (count-free-blocks
             (fa-table-to-alv (set-indices-in-fa-table fa-table nil nil))))
    (fat32-entry-list-p (set-indices-in-fa-table fa-table nil nil))
    (<= (len (set-indices-in-fa-table fa-table nil nil))
        268435447)
    (<= 2
        (len (set-indices-in-fa-table fa-table nil nil))))
   :hints :none)
  (:rewrite l6-wrchs-correctness-1-lemma-26)
  :top :bash :bash
  (:use (:instance find-n-free-clusters-correctness-2
                   (fa-table (set-indices-in-fa-table fa-table nil nil))
                   (n (len (make-blocks (insert-text nil start text))))))
  :pro (:demote 1)
  (:dive 1)
  :x :top :s
  (:bash ("goal" :in-theory (enable set-indices-in-alv)))
  (:dive 1 2)
  (:claim
   (and
    (no-duplicatesp-equal
     (find-n-free-clusters (set-indices-in-fa-table fa-table nil nil)
                           (len (make-blocks (insert-text nil start text)))))
    (feasible-file-length-p
         (len (find-n-free-clusters
                   (set-indices-in-fa-table fa-table nil nil)
                   (len (make-blocks (insert-text nil start text)))))
         (len (insert-text nil start text)))
    (lower-bounded-integer-listp
      (find-n-free-clusters (set-indices-in-fa-table fa-table nil nil)
                            (len (make-blocks (insert-text nil start text))))
      2)
    (bounded-nat-listp
      (find-n-free-clusters (set-indices-in-fa-table fa-table nil nil)
                            (len (make-blocks (insert-text nil start text))))
      (len (set-indices-in-fa-table fa-table nil nil)))
    (<= (len (find-n-free-clusters
                  (set-indices-in-fa-table fa-table nil nil)
                  (len (make-blocks (insert-text nil start text)))))
        (count-free-blocks
             (fa-table-to-alv (set-indices-in-fa-table fa-table nil nil))))
    (fat32-entry-list-p (set-indices-in-fa-table fa-table nil nil))
    (<= (len (set-indices-in-fa-table fa-table nil nil))
        268435447)
    (<= 2
        (len (set-indices-in-fa-table fa-table nil nil))))
   :hints :none)
  (:rewrite l6-wrchs-correctness-1-lemma-26)
  :top :bash :bash
  (:use (:instance find-n-free-clusters-correctness-2
                   (fa-table (set-indices-in-fa-table fa-table nil nil))
                   (n (len (make-blocks (insert-text nil start text))))))
  :pro (:demote 1)
  (:dive 1)
  :x :top :s
  (:bash ("goal" :in-theory (enable set-indices-in-alv)))
  (:demote 26)
  (:dive 1 1)
  (:claim
   (and
    (boolean-listp (fa-table-to-alv fa-table))
    (indices-marked-p
     (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
     (fa-table-to-alv fa-table))
    (no-duplicatesp-equal
     (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))))
    (bounded-nat-listp
     (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
     (len (fa-table-to-alv fa-table))))
   :hints :none)
  (:rewrite l4-wrchs-correctness-1-lemma-18)
  :top :bash :bash
  (:claim
   (and
    (fat32-entry-list-p fa-table)
    (integerp
         (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs))))
    (< (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
       (len fa-table))
    (equal
     (mv-nth
        1
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
     0))
   :hints :none)
  (:rewrite l6-stricter-fs-p-correctness-1-lemma-1)
  :bash :demote :promote
  (:use (:instance l6-wrchs-correctness-1-lemma-59
                   (name (car hns))))
  (:bash ("goal" :in-theory (enable l6-file-index-list)))
  (:use (:instance l6-wrchs-correctness-1-lemma-50
                   (name (car hns))))
  (:bash ("goal" :in-theory (enable l6-file-index-list)))
  (:rewrite make-blocks-correctness-3)
  (:rewrite insert-text-correctness-1)
  (:claim
   (and
    (block-listp
     (fetch-blocks-by-indices
      disk
      (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))))
    (natp (l6-regular-file-length (cdr (assoc-equal (car hns) fs))))
    (feasible-file-length-p
     (len
      (fetch-blocks-by-indices
       disk
       (mv-nth
        0
        (l6-build-index-list
             fa-table
             (l6-regular-file-first-cluster (cdr (assoc-equal (car hns) fs)))
             (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))))
     (l6-regular-file-length (cdr (assoc-equal (car hns) fs)))))
   :hints :none)
  (:rewrite unmake-blocks-correctness-1)
  :bash
  (:use (:instance l6-stat-correctness-1-lemma-9
                   (name (car hns))))
  (:bash ("goal" :in-theory (enable l6-file-index-list)))))

(defthm
  l6-wrchs-correctness-1-lemma-3
  (implies
   (and
    (consp hns)
    (consp fs)
    (consp (assoc-equal (car hns) fs))
    (l6-regular-file-entry-p (cdr (assoc-equal (car hns) fs)))
    (not (cdr hns))
    (>=
     (count-free-blocks
      (fa-table-to-alv
       (set-indices-in-fa-table
        fa-table
        (mv-nth
         0
         (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                             fa-table))
        (make-list-ac
         (len
          (mv-nth
           0
           (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                               fa-table)))
         0 nil))))
     (len
      (make-blocks
       (insert-text
        (unmake-blocks-without-feasibility
         (fetch-blocks-by-indices
          disk
          (mv-nth
           0
           (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                               fa-table)))
         (l6-regular-file-length
          (cdr (assoc-equal (car hns) fs))))
        start text))))
    (consp
     (find-n-free-clusters
      (set-indices-in-fa-table
       fa-table
       (mv-nth
        0
        (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                            fa-table))
       (make-list-ac
        (len
         (mv-nth
          0
          (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                              fa-table)))
        0 nil))
      (len
       (make-blocks
        (insert-text
         (unmake-blocks-without-feasibility
          (fetch-blocks-by-indices
           disk
           (mv-nth
            0
            (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                fa-table)))
          (l6-regular-file-length
           (cdr (assoc-equal (car hns) fs))))
         start text)))))
    (l6-stricter-fs-p fs fa-table)
    (fat32-entry-list-p fa-table)
    (stringp text)
    (integerp start)
    (<= 0 start)
    (symbol-listp hns)
    (block-listp disk)
    (equal (len disk) (len fa-table))
    (<= (len fa-table) *ms-bad-cluster*)
    (<= 2 (len fa-table))
    (<= (len (make-blocks (insert-text nil start text)))
        (count-free-blocks (fa-table-to-alv fa-table))))
   (equal
    (l4-wrchs hns (l6-to-l4-fs-helper fs fa-table)
              disk (fa-table-to-alv fa-table)
              start text)
    (list
     (l6-to-l4-fs-helper
      (mv-nth 0
              (l6-wrchs hns fs disk fa-table start text))
      (mv-nth 2
              (l6-wrchs hns fs disk fa-table start text)))
     (mv-nth 1
             (l6-wrchs hns fs disk fa-table start text))
     (fa-table-to-alv
      (mv-nth 2
              (l6-wrchs hns fs disk fa-table start text))))))
  :hints (("goal" :do-not-induct t)))

;; This theorem shows the equivalence of the l6 and l4 versions of wrchs.
(defthm
  l6-wrchs-correctness-1
  (implies (and (l6-stricter-fs-p fs fa-table)
                (fat32-entry-list-p fa-table)
                (stringp text)
                (natp start)
                (symbol-listp hns)
                (block-listp disk)
                (equal (len disk) (len fa-table))
                (<= (len fa-table) *ms-bad-cluster*)
                (>= (len fa-table) 2))
           (b* (((mv l4-fs-before-write l4-alv-before-write) (l6-to-l4-fs
                                                              fs fa-table))
                ((mv fs-after-write disk-after-write fa-table-after-write)
                 (l6-wrchs hns fs disk fa-table start text))
                ((mv l4-fs-after-write l4-alv-after-write) (l6-to-l4-fs
                                                            fs-after-write fa-table-after-write)))
             (implies
              (<= (len (make-blocks (insert-text nil start text)))
                  (count-free-blocks l4-alv-before-write))
              (equal (l4-wrchs hns l4-fs-before-write disk l4-alv-before-write
                               start text)
                     (mv l4-fs-after-write disk-after-write
                         l4-alv-after-write)))))
  :hints (("goal'5'" :induct (l6-wrchs hns fs disk fa-table start text))
          ("subgoal *1/10'" :in-theory (disable l6-wrchs-correctness-1-lemma-1)
           :use l6-wrchs-correctness-1-lemma-1)
          ("Subgoal *1/7'"
           :expand (len (find-n-free-clusters fa-table 0))
           :in-theory
           (e/d
            (find-n-free-blocks find-n-free-blocks-helper
                                l6-file-index-list set-indices-in-alv
                                set-indices-in-fa-table)
            (l6-wrchs-correctness-1-lemma-7))
           :use
           (:instance
            l6-wrchs-correctness-1-lemma-7
            (fa-table
             (set-indices-in-fa-table
              fa-table
              (mv-nth
               0
               (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                   fa-table))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                     fa-table)))
               0 nil)))
            (n
             (len
              (make-blocks
               (insert-text
                (unmake-blocks
                 (fetch-blocks-by-indices
                  disk
                  (mv-nth
                   0
                   (l6-file-index-list (cdr (assoc-equal (car hns) fs))
                                       fa-table)))
                 (l6-regular-file-length
                  (cdr (assoc-equal (car hns) fs))))
                start text))))))
          ("Subgoal *1/6'" :in-theory (disable l6-wrchs-correctness-1-lemma-3)
           :use l6-wrchs-correctness-1-lemma-3)))
