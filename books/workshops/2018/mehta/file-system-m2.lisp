; Copyright (C) 2017, Regents of the University of Texas
; Written by Mihir Mehta
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

;  file-system-m2.lisp                                  Mihir Mehta

; This is a stobj model of the FAT32 filesystem.

(include-book "generate-index-list")
(include-book "file-system-m1")
(include-book "std/lists/resize-list" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)

(encapsulate
  ()
  (local
   (include-book "std/lists/update-nth" :dir :system))

  (defthm take-of-update-nth
    (equal (take n1 (update-nth n2 val x))
           (if (<= (nfix n1) (nfix n2))
               (take n1 x)
             (update-nth n2 val (take n1 x))))))

(make-event
 `(defstobj fat32-in-memory

    ;; The following fields are noted to be common to both FAT16 and FAT32, per
    ;; the Microsoft specification.
    (bs_jmpboot :type (array (unsigned-byte 8) (3))
                ;; boilerplate
                :initially 0)
    (bs_oemname :type (array (unsigned-byte 8) (8))
                ;; boilerplate
                :initially 0)
    (bpb_bytspersec :type (unsigned-byte 16)
                    ;; per spec
                    :initially ,*ms-min-bytes-per-sector*)
    (bpb_secperclus :type (unsigned-byte 8)
                    ;; boilerplate
                    :initially 0)
    (bpb_rsvdseccnt :type (unsigned-byte 16)
                    ;; per spec
                    :initially 32)
    (bpb_numfats :type (unsigned-byte 8)
                 ;; per spec
                 :initially 2)
    (bpb_rootentcnt :type (unsigned-byte 16)
                    ;; per spec
                    :initially 0)
    (bpb_totsec16 :type (unsigned-byte 16)
                  ;; per spec
                  :initially 0)
    (bpb_media :type (unsigned-byte 8)
               ;; boilerplate
               :initially 0)
    (bpb_fatsz16 :type (unsigned-byte 16)
                 ;; per spec
                 :initially 0)
    (bpb_secpertrk :type (unsigned-byte 16)
                   ;; boilerplate
                   :initially 0)
    (bpb_numheads :type (unsigned-byte 16)
                  ;; boilerplate
                  :initially 0)
    (bpb_hiddsec :type (unsigned-byte 32)
                 ;; boilerplate
                 :initially 0)
    (bpb_totsec32 :type (unsigned-byte 32)
                  ;; boilerplate
                  :initially 0)

    ;; The following fields are noted to be specific to FAT32, per the Microsoft
    ;; specification.
    (bpb_fatsz32 :type (unsigned-byte 32)
                 ;; per spec
                 :initially ,*ms-fat32-min-count-of-clusters*)
    (bpb_extflags :type (unsigned-byte 16)
                  ;; boilerplate
                  :initially 0)
    (bpb_fsver_minor :type (unsigned-byte 8)
               ;; boilerplate
               :initially 0)
    (bpb_fsver_major :type (unsigned-byte 8)
               ;; boilerplate
               :initially 0)
    (bpb_rootclus :type (unsigned-byte 32)
                  ;; per spec
                  :initially ,*ms-first-data-cluster*)
    (bpb_fsinfo :type (unsigned-byte 16)
                ;; per spec
                :initially 1)
    (bpb_bkbootsec :type (unsigned-byte 16)
                   ;; per spec
                   :initially 6)
    (bpb_reserved :type (array (unsigned-byte 8) (12))
                  ;; boilerplate
                  :initially 0)
    (bs_drvnum :type (unsigned-byte 8)
                ;; boilerplate
                :initially 0)
    (bs_reserved1 :type (unsigned-byte 8)
                  ;; boilerplate
                  :initially 0)
    (bs_bootsig :type (unsigned-byte 8)
                ;; boilerplate
                :initially 0)
    (bs_volid :type (unsigned-byte 32)
              ;; boilerplate
              :initially 0)
    (bs_vollab :type (array (unsigned-byte 8) (11))
               ;; boilerplate
               :initially 0)
    (bs_filsystype :type (array (unsigned-byte 8) (8))
                   ;; boilerplate
                   :initially 0)

    ;; The first FAT is placed here. Other copies are not guaranteed to be
    ;; consistent.
    (fat :type (array (unsigned-byte 32) (*ms-fat32-min-count-of-clusters*))
         :resizable t
         ;; per spec
         :initially 0)

    (data-region :type (array (unsigned-byte 8) (*ms-min-data-region-size*))
         :resizable t
         ;; per spec
         :initially 0)))

(defthm bs_oemnamep-alt
  (equal (bs_oemnamep x)
         (unsigned-byte-listp 8 x))
  :rule-classes :definition)

(defthm bs_jmpbootp-alt
  (equal (bs_jmpbootp x)
         (unsigned-byte-listp 8 x))
  :rule-classes :definition)

(defthm bs_vollabp-alt
  (equal (bs_vollabp x)
         (unsigned-byte-listp 8 x))
  :rule-classes :definition)

(defthm bs_filsystypep-alt
  (equal (bs_filsystypep x)
         (unsigned-byte-listp 8 x))
  :rule-classes :definition)

(defthm bpb_reservedp-alt
  (equal (bpb_reservedp x)
         (unsigned-byte-listp 8 x))
  :rule-classes :definition)

(defthm fatp-alt
  (equal (fatp x) (fat32-entry-list-p x))
  :rule-classes :definition
  :hints (("goal" :in-theory (enable fat32-entry-p))))

(defthm data-regionp-alt
  (equal (data-regionp x)
         (unsigned-byte-listp 8 x))
  :rule-classes :definition)

(local
 (in-theory (disable take-of-too-many take-of-len-free make-list-ac-removal
                     revappend-removal)))

(local
 (in-theory (disable bs_oemnamep bs_jmpbootp bs_filsystypep fatp data-regionp)))

(local
 (in-theory (disable bpb_secperclus bpb_fatsz32 bpb_rsvdseccnt
                     bpb_numfats bpb_bytspersec bpb_rootclus bpb_fsinfo
                     bpb_bkbootsec bs_drvnum bs_reserved1 bs_bootsig
                     bpb_media bpb_fsver_major bpb_fsver_major bpb_fatsz16
                     bpb_secpertrk bpb_numheads bpb_rootentcnt
                     bpb_extflags bpb_hiddsec bpb_totsec32 bpb_fatsz32
                     bpb_rootentcnt bpb_totsec16 bs_volid
                     update-bpb_secperclus update-bpb_rsvdseccnt
                     update-bpb_bytspersec update-bpb_numfats
                     update-bpb_rootclus update-bpb_fsinfo update-bpb_bkbootsec
                     update-bs_drvnum update-bs_reserved1 update-bs_bootsig
                     update-bpb_media update-bpb_fsver_minor
                     update-bpb_fsver_major update-bpb_fatsz16
                     update-bpb_secpertrk update-bpb_numheads
                     update-bpb_extflags update-bpb_hiddsec update-bpb_totsec32
                     update-bpb_fatsz32 update-bpb_rootentcnt
                     update-bpb_totsec16 update-bs_volid)))

(local
 (in-theory (disable fati fat-length update-fati resize-fat
                     data-regioni data-region-length update-data-regioni
                     resize-data-region)))

(defmacro
  update-stobj-scalar-correctness
  (bit-width updater accessor
             stobj stobj-recogniser lemma-name1 lemma-name2 lemma-name3)
  `(encapsulate
     nil
     (defthm
       ,lemma-name1
       (implies (and (unsigned-byte-p ,bit-width v)
                     (,stobj-recogniser ,stobj))
                (,stobj-recogniser (,updater v ,stobj)))
       :hints (("goal" :in-theory (enable ,updater))))
     (defthm
       ,lemma-name2
       (implies (,stobj-recogniser ,stobj)
                (unsigned-byte-p ,bit-width (,accessor ,stobj)))
       :hints (("goal" :in-theory (enable ,accessor)))
       :rule-classes
       (:rewrite
        (:rewrite
         :corollary (implies (,stobj-recogniser ,stobj)
                             (integerp (,accessor ,stobj)))
         :hints
         (("goal" :use (:instance unsigned-byte-p-forward-to-nonnegative-integerp
                                  (n ,bit-width)
                                  (x (,accessor ,stobj))))))
        (:rewrite
         :corollary (implies (,stobj-recogniser ,stobj)
                             (rationalp (,accessor ,stobj)))
         :hints
         (("goal" :use (:instance unsigned-byte-p-forward-to-nonnegative-integerp
                                  (n ,bit-width)
                                  (x (,accessor ,stobj))))))))
     (defthm
       ,lemma-name3
       (equal (,accessor (,updater v ,stobj))
              v)
       :hints (("Goal" :in-theory (enable ,accessor ,updater))))))

(update-stobj-scalar-correctness 16 update-bpb_rsvdseccnt bpb_rsvdseccnt
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_rsvdseccnt-correctness-1
                                 update-bpb_rsvdseccnt-correctness-2
                                 update-bpb_rsvdseccnt-correctness-3)

(update-stobj-scalar-correctness 8 update-bpb_secperclus bpb_secperclus
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_secperclus-correctness-1
                                 update-bpb_secperclus-correctness-2
                                 update-bpb_secperclus-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_bytspersec bpb_bytspersec
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_bytspersec-correctness-1
                                 update-bpb_bytspersec-correctness-2
                                 update-bpb_bytspersec-correctness-3)

(update-stobj-scalar-correctness 8 update-bpb_numfats bpb_numfats
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_numfats-correctness-1
                                 update-bpb_numfats-correctness-2
                                 update-bpb_numfats-correctness-3)

(update-stobj-scalar-correctness 32 update-bpb_rootclus bpb_rootclus
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_rootclus-correctness-1
                                 update-bpb_rootclus-correctness-2
                                 update-bpb_rootclus-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_fsinfo bpb_fsinfo
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fsinfo-correctness-1
                                 update-bpb_fsinfo-correctness-2
                                 update-bpb_fsinfo-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_bkbootsec bpb_bkbootsec
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_bkbootsec-correctness-1
                                 update-bpb_bkbootsec-correctness-2
                                 update-bpb_bkbootsec-correctness-3)

(update-stobj-scalar-correctness 8 update-bs_drvnum bs_drvnum
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_drvnum-correctness-1
                                 update-bs_drvnum-correctness-2
                                 update-bs_drvnum-correctness-3)

(update-stobj-scalar-correctness 8 update-bs_reserved1 bs_reserved1
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_reserved1-correctness-1
                                 update-bs_reserved1-correctness-2
                                 update-bs_reserved1-correctness-3)

(update-stobj-scalar-correctness 8 update-bs_bootsig bs_bootsig
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_bootsig-correctness-1
                                 update-bs_bootsig-correctness-2
                                 update-bs_bootsig-correctness-3)

(update-stobj-scalar-correctness 8 update-bpb_media bpb_media
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_media-correctness-1
                                 update-bpb_media-correctness-2
                                 update-bpb_media-correctness-3)

(update-stobj-scalar-correctness 8 update-bpb_fsver_minor bpb_fsver_minor
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fsver_minor-correctness-1
                                 update-bpb_fsver_minor-correctness-2
                                 update-bpb_fsver_minor-correctness-3)

(update-stobj-scalar-correctness 8 update-bpb_fsver_major bpb_fsver_major
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fsver_major-correctness-1
                                 update-bpb_fsver_major-correctness-2
                                 update-bpb_fsver_major-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_fatsz16 bpb_fatsz16
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fatsz16-correctness-1
                                 update-bpb_fatsz16-correctness-2
                                 update-bpb_fatsz16-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_secpertrk bpb_secpertrk
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_secpertrk-correctness-1
                                 update-bpb_secpertrk-correctness-2
                                 update-bpb_secpertrk-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_numheads bpb_numheads
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_numheads-correctness-1
                                 update-bpb_numheads-correctness-2
                                 update-bpb_numheads-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_extflags bpb_extflags
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_extflags-correctness-1
                                 update-bpb_extflags-correctness-2
                                 update-bpb_extflags-correctness-3)

(update-stobj-scalar-correctness 32 update-bpb_hiddsec bpb_hiddsec
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_hiddsec-correctness-1
                                 update-bpb_hiddsec-correctness-2
                                 update-bpb_hiddsec-correctness-3)

(update-stobj-scalar-correctness 32 update-bpb_totsec32 bpb_totsec32
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_totsec32-correctness-1
                                 update-bpb_totsec32-correctness-2
                                 update-bpb_totsec32-correctness-3)

(update-stobj-scalar-correctness 32 update-bpb_fatsz32 bpb_fatsz32
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fatsz32-correctness-1
                                 update-bpb_fatsz32-correctness-2
                                 update-bpb_fatsz32-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_rootentcnt bpb_rootentcnt
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_rootentcnt-correctness-1
                                 update-bpb_rootentcnt-correctness-2
                                 update-bpb_rootentcnt-correctness-3)

(update-stobj-scalar-correctness 16 update-bpb_totsec16 bpb_totsec16
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_totsec16-correctness-1
                                 update-bpb_totsec16-correctness-2
                                 update-bpb_totsec16-correctness-3)

(update-stobj-scalar-correctness 32 update-bs_volid bs_volid
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_volid-correctness-1
                                 update-bs_volid-correctness-2
                                 update-bs_volid-correctness-3)

(defund
  cluster-size (fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (fat32-in-memoryp fat32-in-memory)))
  (* (bpb_secperclus fat32-in-memory)
     (bpb_bytspersec fat32-in-memory)))

(defund
  count-of-clusters (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (and (fat32-in-memoryp fat32-in-memory)
                      (>= (bpb_secperclus fat32-in-memory) 1))
          :guard-debug t))
  (floor (- (bpb_totsec32 fat32-in-memory)
            (+ (bpb_rsvdseccnt fat32-in-memory)
               (* (bpb_numfats fat32-in-memory)
                  (bpb_fatsz32 fat32-in-memory))))
         (bpb_secperclus fat32-in-memory)))

(defund compliant-fat32-in-memoryp (fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory :guard t))
  (and (fat32-in-memoryp fat32-in-memory)
       (>= (bpb_bytspersec fat32-in-memory) *ms-min-bytes-per-sector*)
       (>= (bpb_secperclus fat32-in-memory) 1)
       ;; per spec, although this should be a named constant
       (>= (count-of-clusters fat32-in-memory)
           *ms-fat32-min-count-of-clusters*)
       ;; this isn't in the spec, but clearly implied
       (>= (bpb_rootclus fat32-in-memory) *ms-first-data-cluster*)))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    compliant-fat32-in-memoryp-correctness-1
    (implies (compliant-fat32-in-memoryp fat32-in-memory)
             (and (integerp (cluster-size fat32-in-memory))
                  (>= (cluster-size fat32-in-memory)
                      *ms-min-bytes-per-sector*)
                  (>= (count-of-clusters fat32-in-memory)
                      *ms-fat32-min-count-of-clusters*)
                  (>= (bpb_secperclus fat32-in-memory) 1)
                  (>= (bpb_rootclus fat32-in-memory)
                      *ms-first-data-cluster*)))
    :hints
    (("goal"
      :in-theory (e/d (compliant-fat32-in-memoryp cluster-size)
                      (fat32-in-memoryp))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (integerp (cluster-size fat32-in-memory))))
     (:forward-chaining
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (integerp (cluster-size fat32-in-memory))))
     (:linear
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (and (>= (cluster-size fat32-in-memory)
                        *ms-min-bytes-per-sector*)
                    (>= (count-of-clusters fat32-in-memory)
                        *ms-fat32-min-count-of-clusters*)
                    (>= (bpb_secperclus fat32-in-memory) 1)
                    (>= (bpb_rootclus fat32-in-memory)
                        *ms-first-data-cluster*)))))))

(defthm
  fati-when-compliant-fat32-in-memoryp
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (< (nfix i) (fat-length fat32-in-memory)))
           (fat32-entry-p (fati i fat32-in-memory)))
  :hints (("goal" :in-theory (enable compliant-fat32-in-memoryp
                                     fati fat-length))))

;; Per accumulated-persistence, the rule (:rewrite
;; update-bpb_secperclus-correctness-2 . 3) is pretty darned useless. We need
;; to find a way to do without it and its kind.
(encapsulate
  ()

  (local
   (defun
       make-corollary
       (accessor1 updater2 constant2 stobj)
     (list ':rewrite
           ':corollary
           (list 'implies
                 (list 'equal 'key constant2)
                 (list 'equal
                       (list accessor1 (list updater2 'val stobj))
                       (list accessor1 stobj)))
           ':hints
           (list (list '"goal"
                       ':in-theory
                       (list 'enable updater2))))))

  (local
   (defun
       make-corollaries
       (accessor1 updaters-constants stobj)
     (if (atom updaters-constants)
         (list ':rewrite)
       (list*
        (make-corollary
         accessor1
         (caar updaters-constants)
         (cdar updaters-constants)
         stobj)
        (make-corollaries
         accessor1 (cdr updaters-constants) stobj)))))

  (local
   (defconst *the-list*
     (list
      (cons 'update-bpb_fatsz32 *bpb_fatsz32*)
      (cons 'update-bpb_bytspersec *bpb_bytspersec*)
      (cons 'update-bpb_rsvdseccnt *bpb_rsvdseccnt*)
      (cons 'update-bpb_rootclus *bpb_rootclus*)
      (cons 'update-bs_bootsig *bs_bootsig*)
      (cons 'update-bs_reserved1 *bs_reserved1*)
      (cons 'update-bs_drvnum *bs_drvnum*)
      (cons 'update-bpb_bkbootsec *bpb_bkbootsec*)
      (cons 'update-bpb_fsinfo *bpb_fsinfo*)
      (cons 'update-bpb_fsver_major *bpb_fsver_major*)
      (cons 'update-bpb_fsver_minor *bpb_fsver_minor*)
      (cons 'update-bpb_extflags *bpb_extflags*)
      (cons 'update-bpb_secperclus *bpb_secperclus*)
      (cons 'update-bpb_totsec32 *bpb_totsec32*)
      (cons 'update-bpb_hiddsec *bpb_hiddsec*)
      (cons 'update-bpb_numheads *bpb_numheads*)
      (cons 'update-bpb_secpertrk *bpb_secpertrk*)
      (cons 'update-bpb_fatsz16 *bpb_fatsz16*)
      (cons 'update-bpb_media *bpb_media*)
      (cons 'update-bpb_totsec16 *bpb_totsec16*)
      (cons 'update-bpb_rootentcnt *bpb_rootentcnt*)
      (cons 'update-bpb_numfats *bpb_numfats*)
      (cons 'update-bs_volid *bs_volid*))))

  (make-event
   `(defthm
      bpb_fatsz32-of-update-nth
      (implies
       (not (equal key *bpb_fatsz32*))
       (equal
        (bpb_fatsz32 (update-nth key val fat32-in-memory))
        (bpb_fatsz32 fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_fatsz32)))
      :rule-classes
      ,(make-corollaries
        'bpb_fatsz32
        (remove1-assoc 'update-bpb_fatsz32 *the-list*)
        'fat32-in-memory)))

  (make-event
   `(defthm
      bpb_secperclus-of-update-nth
      (implies
       (not (equal key *bpb_secperclus*))
       (equal (bpb_secperclus (update-nth key val fat32-in-memory))
              (bpb_secperclus fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_secperclus)))
      :rule-classes
      ,(make-corollaries
        'bpb_secperclus
        (remove1-assoc 'update-bpb_secperclus *the-list*)
        'fat32-in-memory)))

  (make-event
   `(defthm
      bpb_rsvdseccnt-of-update-nth
      (implies
       (not (equal key *bpb_rsvdseccnt*))
       (equal
        (bpb_rsvdseccnt (update-nth key val fat32-in-memory))
        (bpb_rsvdseccnt fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_rsvdseccnt)))
      :rule-classes
      ,(make-corollaries
        'bpb_rsvdseccnt
        (remove1-assoc 'update-bpb_rsvdseccnt *the-list*)
        'fat32-in-memory)))

  (make-event
   `(defthm
      bpb_numfats-of-update-nth
      (implies
       (not (equal key *bpb_numfats*))
       (equal
        (bpb_numfats (update-nth key val fat32-in-memory))
        (bpb_numfats fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_numfats)))
      :rule-classes
      ,(make-corollaries
        'bpb_numfats
        (remove1-assoc 'update-bpb_numfats *the-list*)
        'fat32-in-memory)))

  (make-event
   `(defthm
      bpb_bytspersec-of-update-nth
      (implies
       (not (equal key *bpb_bytspersec*))
       (equal
        (bpb_bytspersec (update-nth key val fat32-in-memory))
        (bpb_bytspersec fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_bytspersec)))
      :rule-classes
      ,(make-corollaries
        'bpb_bytspersec
        (remove1-assoc 'update-bpb_bytspersec *the-list*)
        'fat32-in-memory)))

  (make-event
   `(defthm
      bpb_totsec32-of-update-nth
      (implies
       (not (equal key *bpb_totsec32*))
       (equal
        (bpb_totsec32 (update-nth key val fat32-in-memory))
        (bpb_totsec32 fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_totsec32)))
      :rule-classes
      ,(make-corollaries
        'bpb_totsec32
        (remove1-assoc 'update-bpb_totsec32 *the-list*)
        'fat32-in-memory)))

  (make-event
   `(defthm
      bpb_rootclus-of-update-nth
      (implies
       (not (equal key *bpb_rootclus*))
       (equal
        (bpb_rootclus (update-nth key val fat32-in-memory))
        (bpb_rootclus fat32-in-memory)))
      :hints (("goal" :in-theory (enable bpb_rootclus)))
      :rule-classes
      ,(make-corollaries
        'bpb_rootclus
        (remove1-assoc 'update-bpb_rootclus *the-list*)
        'fat32-in-memory))))

(defthm
  cluster-size-of-update-fati
  (equal (cluster-size (update-fati i v fat32-in-memory))
         (cluster-size fat32-in-memory))
  :hints
  (("goal" :in-theory (enable cluster-size update-fati))))

(defthm
  fat-length-of-update-fati
  (equal (fat-length (update-fati i v fat32-in-memory))
         (max (fat-length fat32-in-memory)
              (1+ (nfix i))))
  :hints (("goal" :in-theory (enable fat-length update-fati))))

(defthm
  fat-length-of-resize-fat
  (equal (fat-length (resize-fat i fat32-in-memory))
         (nfix i))
  :hints (("goal" :in-theory (enable fat-length resize-fat))))

(defthm
  count-of-clusters-of-update-fati
  (equal (count-of-clusters (update-fati i v fat32-in-memory))
         (count-of-clusters fat32-in-memory))
  :hints
  (("goal"
    :in-theory (e/d (count-of-clusters update-fati bpb_totsec32)
                    (floor)))))

(defthm
  compliant-fat32-in-memoryp-of-update-fati
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (< i (fat-length fat32-in-memory)))
           (equal
            (compliant-fat32-in-memoryp
             (update-fati i v fat32-in-memory))
            (fat32-entry-p v)))
  :hints
  (("goal"
    :in-theory (e/d (compliant-fat32-in-memoryp
                     update-fati fat-length count-of-clusters)
                    (floor)))))

(defthm
  data-regioni-when-compliant-fat32-in-memoryp
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (< (nfix i) (data-region-length fat32-in-memory)))
           (unsigned-byte-p 8 (data-regioni i fat32-in-memory)))
  :hints (("goal" :in-theory (e/d (compliant-fat32-in-memoryp
                                   data-regioni data-region-length)
                                  (unsigned-byte-p)))))

(defthm
  compliant-fat32-in-memoryp-of-update-data-regioni
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (< i (data-region-length fat32-in-memory)))
           (equal
            (compliant-fat32-in-memoryp
             (update-data-regioni i v fat32-in-memory))
            (unsigned-byte-p 8 v)))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (compliant-fat32-in-memoryp
                     update-data-regioni
                     data-region-length count-of-clusters)
                    (floor)))))

(defthm
  data-region-length-of-update-data-regioni
  (implies
   (< (nfix i) (data-region-length fat32-in-memory))
   (equal (data-region-length
           (update-data-regioni i v fat32-in-memory))
          (data-region-length fat32-in-memory)))
  :hints (("goal" :in-theory (enable data-region-length
                                     update-data-regioni))))

(defthm
  data-region-length-of-resize-data-region
  (equal (data-region-length
          (resize-data-region i data-region32-in-memory))
         (nfix i))
  :hints (("goal" :in-theory (enable data-region-length
                                     resize-data-region))))

(defconst *initialbytcnt* 16)

(defthm
  nthcdr-past-end
  (implies (and (integerp n)
                (true-listp l)
                (>= n (len l)))
           (not (nthcdr n l)))
  :hints
  (("subgoal *1/5.1'" :in-theory (disable nthcdr-of-cdr)
    :use (:instance nthcdr-of-cdr (i (- n 1))
                    (x nil)))))

(defmacro
  reason-about-stobj-array
    (name1 name2
           array-length bit-width array-updater array-accessor
           stobj-position-constant array-length-constant
           stobj stobj-recogniser
           lemma-name1 lemma-name2 lemma-name3 lemma-name4 lemma-name5)
  `(encapsulate
     nil

     (defun
       ,name1 (v ,stobj)
       (declare
        (xargs
         :guard (and (unsigned-byte-listp ,bit-width v)
                     (<= (len v)
                         (,array-length ,stobj))
                     (,stobj-recogniser ,stobj))
         :guard-hints
         (("goal" :in-theory (disable ,stobj-recogniser unsigned-byte-p nth)))
         :stobjs (,stobj)))
       (if
           (atom v)
           ,stobj
        (let* ((,stobj
                (,array-updater (- (,array-length ,stobj)
                                       (len v))
                                (car v)
                                ,stobj))
               (,stobj (,name1 (cdr v)
                              ,stobj)))
          ,stobj)))

     (defun
       ,name2 (,stobj i)
       (declare
        (xargs :stobjs ,stobj
               :guard (and (,stobj-recogniser ,stobj)
                           (natp i)
                           (<= i
                               (,array-length ,stobj)))))
       (if (zp i)
           nil
         (cons (,array-accessor (- (,array-length ,stobj)
                                   i)
                                ,stobj)
                 (,name2 ,stobj (- i 1)))))

     (defthm
       ,lemma-name1
       t
       :rule-classes
       ((:rewrite :corollary
                   (equal (bpb_secperclus (,name1 v ,stobj))
                          (bpb_secperclus fat32-in-memory))
                   :hints (("Goal" :in-theory (enable bpb_secperclus)) ))
        (:rewrite :corollary
                   (equal (bpb_rsvdseccnt (,name1 v ,stobj))
                          (bpb_rsvdseccnt fat32-in-memory))
                  :hints (("Goal" :in-theory (enable bpb_rsvdseccnt)) ))
        (:rewrite :corollary
                   (equal (bpb_numfats (,name1 v ,stobj))
                          (bpb_numfats fat32-in-memory))
                  :hints (("Goal" :in-theory (enable bpb_numfats)) ))
        (:rewrite :corollary
                   (equal (bpb_fatsz32 (,name1 v ,stobj))
                          (bpb_fatsz32 fat32-in-memory))
                  :hints (("Goal" :in-theory (enable bpb_fatsz32)) ))
        (:rewrite :corollary
                   (equal (bpb_bytspersec (,name1 v ,stobj))
                          (bpb_bytspersec fat32-in-memory))
                   :hints (("Goal" :in-theory (enable bpb_bytspersec)) ))
        (:rewrite :corollary
                   (equal (bpb_totsec32 (,name1 v ,stobj))
                          (bpb_totsec32 fat32-in-memory))
                   :hints (("Goal" :in-theory (enable bpb_totsec32)) ))))

     (defthm
       ,lemma-name2 t
       :rule-classes
       ((:rewrite
         :corollary
         (implies
          (and (,stobj-recogniser ,stobj)
               (integerp i)
               (<= 0 i)
               (< i (,array-length ,stobj))
               (unsigned-byte-p ,bit-width v))
          (,stobj-recogniser (,array-updater i v ,stobj))))
        (:rewrite
         :corollary
         (implies
          (and (,stobj-recogniser ,stobj)
               (integerp i)
               (<= 0 i)
               (< i (,array-length ,stobj))
               (unsigned-byte-p ,bit-width v))
          (equal (len (nth ,stobj-position-constant
                           (,array-updater i v ,stobj)))
                 (len (nth ,stobj-position-constant ,stobj)))))))

     (defthm ,lemma-name3
       (implies (and (unsigned-byte-listp ,bit-width v)
                     (<= (len v)
                         (,array-length ,stobj))
                     (,stobj-recogniser ,stobj))
                (,stobj-recogniser (,name1 v ,stobj)))
       :hints (("goal" :in-theory (e/d (unsigned-byte-listp)
                                       (,stobj-recogniser ,array-updater))
                :induct
                (,stobj-recogniser (,name1 v ,stobj)))))

     (defthm ,lemma-name4
       (implies (and (,stobj-recogniser ,stobj)
                     (integerp i)
                     (<= 0 i)
                     (< i (,array-length ,stobj)))
                (unsigned-byte-p ,bit-width (,array-accessor i ,stobj)))
       :hints (("Goal" :in-theory (disable nth unsigned-byte-p))))

     (defthm ,lemma-name5
       (implies (and (,stobj-recogniser ,stobj)
                     (integerp i)
                     (<= 0 i)
                     (<= i (,array-length ,stobj)))
                (equal (,name2 ,stobj i)
                       (nthcdr (- (,array-length ,stobj)
                                  i)
                               (nth ,stobj-position-constant ,stobj))))
       :hints
       (("Subgoal *1/2"
         :in-theory (disable nth-of-nthcdr nthcdr-of-cdr)
         :use ((:instance nth-of-nthcdr (n 0)
                          (m (- ,array-length-constant i))
                          (x (nth ,stobj-position-constant ,stobj)))
               (:instance nthcdr-of-cdr (i (+ ,array-length-constant (- i)))
                          (x (nth ,stobj-position-constant ,stobj)))))))))

(reason-about-stobj-array
 update-bs_jmpboot bs_jmpboot-suffix
 bs_jmpboot-length 8 update-bs_jmpbooti
 bs_jmpbooti *bs_jmpbooti*
 3 fat32-in-memory fat32-in-memoryp
 update-bs_jmpboot-correctness-1
 update-bs_jmpboot-correctness-2
 update-bs_jmpboot-correctness-3
 update-bs_jmpboot-correctness-4
 bs_jmpboot-suffix-correctness-1)

(reason-about-stobj-array
 update-bs_oemname bs_oemname-suffix
 bs_oemname-length 8 update-bs_oemnamei
 bs_oemnamei *bs_oemnamei*
 8 fat32-in-memory fat32-in-memoryp
 update-bs_oemname-correctness-1
 update-bs_oemname-correctness-2
 update-bs_oemname-correctness-3
 update-bs_oemname-correctness-4
 bs_oemname-suffix-correctness-1)

(defthm
  update-bs_oemname-correctness-5
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal (fat32-in-memoryp
           (update-nth *bs_oemnamei* v fat32-in-memory))
          (and (unsigned-byte-listp 8 v)
               (equal (len v) 8)))))

(reason-about-stobj-array
 update-bs_vollab bs_vollab-suffix
 bs_vollab-length 8 update-bs_vollabi
 bs_vollabi *bs_vollabi*
 11 fat32-in-memory fat32-in-memoryp
 update-bs_vollab-correctness-1
 update-bs_vollab-correctness-2
 update-bs_vollab-correctness-3
 update-bs_vollab-correctness-4
 bs_vollab-suffix-correctness-1)

(reason-about-stobj-array
 update-bs_filsystype
 bs_filsystype-suffix
 bs_filsystype-length
 8 update-bs_filsystypei
 bs_filsystypei *bs_filsystypei*
 8 fat32-in-memory fat32-in-memoryp
 update-bs_filsystype-correctness-1
 update-bs_filsystype-correctness-2
 update-bs_filsystype-correctness-3
 update-bs_filsystype-correctness-4
 bs_filsystype-suffix-correctness-1)

(reason-about-stobj-array
 update-bpb_reserved
 bpb_reserved-suffix bpb_reserved-length
 8 update-bpb_reservedi
 bpb_reservedi *bpb_reservedi*
 12 fat32-in-memory fat32-in-memoryp
 update-bpb_reserved-correctness-1
 update-bpb_reserved-correctness-2
 update-bpb_reserved-correctness-3
 update-bpb_reserved-correctness-4
 bpb_reserved-suffix-correctness-1)

(defthm
  read-reserved-area-guard-lemma-1
  (implies (and (member-equal x
                              (mv-nth 0 (read-byte$-n n channel state)))
                (state-p1 state)
                (symbolp channel)
                (open-input-channel-p1 channel
                                       :byte state)
                (not (equal (mv-nth 0 (read-byte$-n n channel state))
                            'fail)))
           (unsigned-byte-p 8 x))
  :rule-classes :forward-chaining)

(defthm
  read-reserved-area-guard-lemma-2
  (implies
   (and (natp n)
        (< (nfix m) n)
        (state-p1 state)
        (symbolp channel)
        (open-input-channel-p1 channel
                               :byte state)
        (not (equal (mv-nth 0 (read-byte$-n n channel state))
                    'fail)))
   (unsigned-byte-p
    8
    (nth m
         (mv-nth 0 (read-byte$-n n channel state)))))
  :hints
  (("goal"
    :in-theory (disable unsigned-byte-p nth)
    :use
    (:instance
     read-reserved-area-guard-lemma-1
     (x (nth m
             (mv-nth 0 (read-byte$-n n channel state))))))))

(defthm
  read-reserved-area-guard-lemma-3
  (implies
   (and (state-p1 state)
        (symbolp channel)
        (open-input-channel-p1 channel
                               :byte state)
        (not (equal (mv-nth 0 (read-byte$-n n channel state))
                    'fail)))
   (unsigned-byte-listp
    8
    (mv-nth 0 (read-byte$-n n channel state))))
  :hints (("goal" :in-theory (disable unsigned-byte-p))))

(defthm
  read-reserved-area-guard-lemma-4
  (equal (stringp (mv-nth 0 (read-byte$-n n channel state)))
         nil)
  :hints (("goal" :in-theory (disable read-byte$-n-data)
           :use read-byte$-n-data)))

(defund get-initial-bytes (str)
  (declare (xargs :guard (and (stringp str)
                              (>= (length str) *initialbytcnt*))))
  (string=>nats (subseq str 0 *initialbytcnt*)))

(defthm
  get-initial-bytes-correctness-1
  (implies (stringp str)
           (equal (len (get-initial-bytes str))
                  *initialbytcnt*))
  :hints (("goal" :in-theory (enable get-initial-bytes))))

(defthm
  get-initial-bytes-correctness-2
           (unsigned-byte-listp 8 (get-initial-bytes str))
  :hints (("goal" :in-theory (enable get-initial-bytes))))

(defthm
  nth-of-get-initial-bytes
  (implies (stringp str)
           (equal (integerp (nth n (get-initial-bytes str)))
                  (< (nfix n) *initialbytcnt*)))
  :hints (("goal" :in-theory (enable get-initial-bytes))))

(defund
  get-remaining-rsvdbyts (str)
  (declare
   (xargs
    :guard
    (and
     (stringp str)
     (>= (length str) *initialbytcnt*)
     (<= (* (combine16u (nth 12 (get-initial-bytes str))
                        (nth 11 (get-initial-bytes str)))
            (combine16u (nth 15 (get-initial-bytes str))
                        (nth 14 (get-initial-bytes str))))
         (length str))
     (<= *initialbytcnt*
         (* (combine16u (nth 12 (get-initial-bytes str))
                        (nth 11 (get-initial-bytes str)))
            (combine16u (nth 15 (get-initial-bytes str))
                        (nth 14 (get-initial-bytes str))))))))
  (b*
      ((initial-bytes (get-initial-bytes str))
       (tmp_bytspersec (combine16u (nth (+ 11 1) initial-bytes)
                                   (nth (+ 11 0) initial-bytes)))
       (tmp_rsvdseccnt (combine16u (nth (+ 14 1) initial-bytes)
                                   (nth (+ 14 0) initial-bytes)))
       (tmp_rsvdbytcnt (* tmp_rsvdseccnt tmp_bytspersec)))
    (string=>nats (subseq str *initialbytcnt* tmp_rsvdbytcnt))))

(defthm
  get-remaining-rsvdbyts-correctness-1
  (implies
   (stringp str)
   (equal
    (len (get-remaining-rsvdbyts str))
    (nfix
     (+ -16
        (* (combine16u (nth 12 (get-initial-bytes str))
                       (nth 11 (get-initial-bytes str)))
           (combine16u (nth 15 (get-initial-bytes str))
                       (nth 14 (get-initial-bytes str))))))))
  :hints (("goal" :in-theory (enable get-remaining-rsvdbyts))))

(defthm
  get-remaining-rsvdbyts-correctness-2
           (unsigned-byte-listp 8 (get-remaining-rsvdbyts str))
  :hints (("goal" :in-theory (enable get-remaining-rsvdbyts))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (local
   (defthm read-reserved-area-guard-lemma-5
     (implies (and (unsigned-byte-listp 8 l)
                   (natp n)
                   (< n (len l)))
              (rationalp (nth n l)))))

  ;; This must be called after the file is opened.
  (defun
      read-reserved-area (fat32-in-memory str)
    (declare
     (xargs
      :guard (and (stringp str)
                  (>= (length str) *initialbytcnt*)
                  (fat32-in-memoryp fat32-in-memory))
      :guard-hints
      (("goal"
        :do-not-induct t
        :in-theory (disable fat32-in-memoryp unsigned-byte-p nth))
       ("subgoal 7" :in-theory (disable unsigned-byte-p-of-nth-when-unsigned-byte-listp)
        :use ((:instance
               unsigned-byte-p-of-nth-when-unsigned-byte-listp
               (n 13)
               (l (get-initial-bytes str))
               (bits 8))
              (:instance unsigned-byte-p-forward-to-nonnegative-integerp
                         (n bits)
                         (x (nth 13 (get-initial-bytes str))))))
       ("subgoal 6" :in-theory (disable unsigned-byte-p-of-nth-when-unsigned-byte-listp)
        :use (:instance
              unsigned-byte-p-of-nth-when-unsigned-byte-listp
              (n 0)
              (l (get-remaining-rsvdbyts str))
              (bits 8))))
      :stobjs (fat32-in-memory)))
    (b*
        (;; we want to do this unconditionally, in order to prove a strong linear
         ;; rule
         (fat32-in-memory
          (update-bpb_secperclus 1
                                 fat32-in-memory))
         ;; also needs to be unconditional
         (fat32-in-memory
          (update-bpb_rsvdseccnt 1
                                 fat32-in-memory))
         ;; also needs to be unconditional
         (fat32-in-memory
          (update-bpb_numfats 1
                              fat32-in-memory))
         ;; I feel weird about stipulating this, but the FAT size has to be at
         ;; least 1 if we're going to have at least 65536 clusters of data.
         (fat32-in-memory
          (update-bpb_fatsz32 1
                              fat32-in-memory))
         ;; This needs to be at least 512, per the spec.
         (fat32-in-memory
          (update-bpb_bytspersec 512
                                 fat32-in-memory))
         ;; common stuff for fat filesystems
         (initial-bytes
          (get-initial-bytes str))
         (fat32-in-memory
          (update-bs_jmpboot (subseq initial-bytes 0 3) fat32-in-memory))
         (fat32-in-memory
          (update-bs_oemname (subseq initial-bytes 3 11) fat32-in-memory))
         (tmp_bytspersec (combine16u (nth (+ 11 1) initial-bytes)
                                     (nth (+ 11 0) initial-bytes)))
         ((unless (>= tmp_bytspersec 512))
          (mv fat32-in-memory -1))
         (fat32-in-memory
          (update-bpb_bytspersec tmp_bytspersec fat32-in-memory))
         (tmp_secperclus (nth 13 initial-bytes))
         ;; this is actually a proxy for testing membership in the set {1, 2, 4,
         ;; 8, 16, 32, 64, 128}
         ((unless (>= tmp_secperclus 1))
          (mv fat32-in-memory -1))
         (fat32-in-memory
          (update-bpb_secperclus tmp_secperclus
                                 fat32-in-memory))
         (tmp_rsvdseccnt (combine16u (nth (+ 14 1) initial-bytes)
                                     (nth (+ 14 0) initial-bytes)))
         ((unless (>= tmp_rsvdseccnt 1))
          (mv fat32-in-memory -1))
         (fat32-in-memory
          (update-bpb_rsvdseccnt tmp_rsvdseccnt fat32-in-memory))
         (tmp_rsvdbytcnt (* tmp_rsvdseccnt tmp_bytspersec))
         ((unless (and (>= tmp_rsvdbytcnt *initialbytcnt*)
                       (>= (length str) tmp_rsvdbytcnt)))
          (mv fat32-in-memory -1))
         (remaining-rsvdbyts
          (get-remaining-rsvdbyts str))
         (tmp_numfats (nth (- 16 *initialbytcnt*) remaining-rsvdbyts))
         ((unless (>= tmp_numfats 1))
          (mv fat32-in-memory -1))
         (fat32-in-memory
          (update-bpb_numfats tmp_numfats
                              fat32-in-memory))
         (fat32-in-memory
          (update-bpb_rootentcnt
           (combine16u (nth (+ 17 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 17 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_totsec16
           (combine16u (nth (+ 19 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 19 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_media (nth (- 21 *initialbytcnt*) remaining-rsvdbyts)
                            fat32-in-memory))
         (fat32-in-memory
          (update-bpb_fatsz16
           (combine16u (nth (+ 22 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 22 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_secpertrk
           (combine16u (nth (+ 24 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 24 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_numheads
           (combine16u (nth (+ 26 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 26 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_hiddsec
           (combine32u (nth (+ 28 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 28 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 28 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 28 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_totsec32
           (combine32u (nth (+ 32 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 32 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 32 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 32 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         ;; fat32-specific stuff
         (tmp_fatsz32
          (combine32u (nth (+ 36 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                      (nth (+ 36 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                      (nth (+ 36 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                      (nth (+ 36 0 (- *initialbytcnt*)) remaining-rsvdbyts)))
         ((unless (>= tmp_fatsz32 1))
          (mv fat32-in-memory -1))
         (fat32-in-memory
          (update-bpb_fatsz32
           tmp_fatsz32
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_extflags
           (combine16u (nth (+ 40 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 40 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_fsver_minor (nth (- 42 *initialbytcnt*) remaining-rsvdbyts)
                                  fat32-in-memory))
         (fat32-in-memory
          (update-bpb_fsver_major (nth (- 43 *initialbytcnt*) remaining-rsvdbyts)
                                  fat32-in-memory))
         (fat32-in-memory
          (update-bpb_rootclus
           (combine32u (nth (+ 44 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 44 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 44 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 44 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_fsinfo
           (combine16u (nth (+ 48 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 48 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bpb_bkbootsec
           (combine16u (nth (+ 50 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 50 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         ;; skipping bpb_reserved for now
         (fat32-in-memory
          (update-bs_drvnum (nth (- 64 *initialbytcnt*) remaining-rsvdbyts)
                            fat32-in-memory))
         (fat32-in-memory
          (update-bs_reserved1 (nth (- 65 *initialbytcnt*) remaining-rsvdbyts)
                               fat32-in-memory))
         (fat32-in-memory
          (update-bs_bootsig (nth (- 66 *initialbytcnt*) remaining-rsvdbyts)
                             fat32-in-memory))
         (fat32-in-memory
          (update-bs_volid
           (combine32u (nth (+ 67 3 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 67 2 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 67 1 (- *initialbytcnt*)) remaining-rsvdbyts)
                       (nth (+ 67 0 (- *initialbytcnt*)) remaining-rsvdbyts))
           fat32-in-memory))
         (fat32-in-memory
          (update-bs_vollab (subseq remaining-rsvdbyts
                                    (+ 71 (- *initialbytcnt*) 0)
                                    (+ 71 (- *initialbytcnt*) 11)) fat32-in-memory))
         (fat32-in-memory
          (update-bs_filsystype (subseq remaining-rsvdbyts
                                        (+ 82 (- *initialbytcnt*) 0)
                                        (+ 82 (- *initialbytcnt*) 8)) fat32-in-memory)))
      (mv fat32-in-memory 0))))

(defthm
  read-fat-guard-lemma-1
  (implies
   (and (state-p1 state)
        (symbolp channel)
        (open-input-channel-p1 channel
                               :byte state)
        (not (equal (mv-nth 0 (read-32ule-n n channel state))
                    'fail)))
   (unsigned-byte-listp
    32
    (mv-nth 0 (read-32ule-n n channel state))))
  :hints (("goal" :in-theory (disable unsigned-byte-p))))

(defun
  update-data-region
  (fat32-in-memory str len pos)
  (declare
   (xargs :guard (and (stringp str)
                      (natp len)
                      (natp pos)
                      (<= pos len)
                      (= len (length str))
                      (<= len
                          (data-region-length fat32-in-memory))
                      (<= (data-region-length fat32-in-memory)
                          *ms-max-data-region-size*))
          :guard-hints
          (("goal"
            :in-theory (e/d (data-region-length update-data-regioni)
                            (fat32-in-memoryp))))
          :guard-debug t
          :measure (nfix (- len pos))
          :stobjs fat32-in-memory))
  (b*
      ((len (the (unsigned-byte 47) len))
       (pos (the (unsigned-byte 47) pos)))
    (if
     (mbe :logic (zp (- len pos))
          :exec (>= pos len))
     fat32-in-memory
     (b*
         ((ch (char str pos))
          (ch-byte (the (unsigned-byte 8) (char-code ch)))
          (pos+1 (the (unsigned-byte 47) (1+ pos)))
          (fat32-in-memory
           (update-data-regioni pos ch-byte fat32-in-memory)))
       (update-data-region fat32-in-memory str len pos+1)))))

(defun
  update-fat (fat32-in-memory str pos)
  (declare
   (xargs :guard (and (stringp str)
                      (natp pos)
                      (<= (* pos 4) (length str))
                      (equal (length str)
                             (* (fat-length fat32-in-memory) 4))
                      (<= pos *ms-bad-cluster*))
          :guard-hints
          (("goal" :in-theory (e/d (fat-length update-fati)
                                   (fat32-in-memoryp))))
          :guard-debug t
          :stobjs fat32-in-memory))
  (b*
      ((pos (the (unsigned-byte 28) pos)))
    (if
     (zp pos)
     fat32-in-memory
     (b*
         ((ch-word
           (the
            (unsigned-byte 32)
            (combine32u (char-code (char str
                                         (the (unsigned-byte 30)
                                              (- (* pos 4) 1))))
                        (char-code (char str
                                         (the (unsigned-byte 30)
                                              (- (* pos 4) 2))))
                        (char-code (char str
                                         (the (unsigned-byte 30)
                                              (- (* pos 4) 3))))
                        (char-code (char str
                                         (the (unsigned-byte 30)
                                              (- (* pos 4) 4)))))))
          (fat32-in-memory (update-fati (- pos 1)
                                        ch-word fat32-in-memory)))
       (update-fat fat32-in-memory str
                   (the (unsigned-byte 28) (- pos 1)))))))

(defthm
  read-fat-guard-lemma-2
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (<= 0 (bpb_fatsz32 fat32-in-memory)))
  :hints (("Goal" :use update-bpb_fatsz32-correctness-2) )
  :rule-classes :linear)

(defthm
  read-fat-guard-lemma-3
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (<= 0 (bpb_bytspersec fat32-in-memory)))
  :hints (("Goal" :use update-bpb_bytspersec-correctness-2) )
  :rule-classes :linear)

(defthm
  slurp-disk-image-guard-lemma-2
  (implies (member n
                   (list *bpb_secperclus*
                         *bpb_fatsz32* *bpb_numfats*
                         *bpb_rsvdseccnt* *data-regioni*))
           (equal (nth n (update-fat fat32-in-memory str pos))
                  (nth n fat32-in-memory)))
  :hints (("goal" :in-theory (enable update-fat update-fati))))

(defthm slurp-disk-image-guard-lemma-3
  (equal (bpb_secperclus
              (update-fat fat32-in-memory str pos))
         (bpb_secperclus fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_secperclus)) ))

(defthm slurp-disk-image-guard-lemma-4
  (equal (bpb_fatsz32
              (update-fat fat32-in-memory str pos))
         (bpb_fatsz32 fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_fatsz32)) ))

(defthm slurp-disk-image-guard-lemma-5
  (equal (bpb_numfats
              (update-fat fat32-in-memory str pos))
         (bpb_numfats fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_numfats)) ))

(defthm slurp-disk-image-guard-lemma-6
  (equal (bpb_rsvdseccnt
              (update-fat fat32-in-memory str pos))
         (bpb_rsvdseccnt fat32-in-memory))
  :hints (("Goal" :in-theory (enable bpb_rsvdseccnt)) ))

;; BOZO: Remove these.

(defthm
  slurp-disk-image-guard-lemma-11
  (implies (and (integerp x) (integerp y))
           (integerp (+ x y))))

(defthm
  slurp-disk-image-guard-lemma-12
  (implies (and (integerp x) (integerp y))
           (integerp (* x y))))

;; (defun m2-stricter-fs-p (fat32-in-memory)
;;   (declare (xargs :guard t))
;;   (and (fat32-in-memoryp fat32-in-memory)
;;        (<= 1
;;            (bpb_secperclus fat32-in-memory))
;;        (<= 1
;;            (bpb_rsvdseccnt fat32-in-memory))))

(defthm
  bpb_secperclus-of-read-reserved-area t
  :rule-classes
  ((:linear
    :corollary
    (<= 1
        (bpb_secperclus
         (mv-nth 0
                 (read-reserved-area fat32-in-memory str))))
    :hints
    (("goal" :do-not-induct t
      :in-theory (disable fat32-in-memoryp nth subseq))))
   (:rewrite
    :corollary
    (implies
     (stringp str)
     (integerp
      (bpb_secperclus
       (mv-nth 0
               (read-reserved-area fat32-in-memory str)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable fat32-in-memoryp nth subseq))))))

(defthm
  slurp-disk-image-guard-lemma-14
  (<= 1
      (bpb_rsvdseccnt
       (mv-nth
        0
        (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable fat32-in-memoryp nth subseq))))

(defthm
  slurp-disk-image-guard-lemma-15
  (<= 1
      (bpb_numfats
       (mv-nth
        0
        (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable fat32-in-memoryp nth subseq))))

(defthm
  slurp-disk-image-guard-lemma-16
  (<= 1
      (bpb_fatsz32
       (mv-nth
        0
        (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable fat32-in-memoryp nth subseq))))

(defthm
  slurp-disk-image-guard-lemma-17
  (<= *ms-min-bytes-per-sector*
      (bpb_bytspersec
       (mv-nth
        0
        (read-reserved-area fat32-in-memory str))))
  :rule-classes :linear
  :hints (("goal" :do-not-induct t
           :in-theory (disable fat32-in-memoryp nth subseq))))

(defthm bpb_rsvdseccnt-of-resize-fat
  (equal (bpb_rsvdseccnt (resize-fat i fat32-in-memory))
         (bpb_rsvdseccnt fat32-in-memory))
  :hints (("goal" :in-theory (enable resize-fat))))

(defthm bpb_bytspersec-of-resize-fat
  (equal (bpb_bytspersec (resize-fat i fat32-in-memory))
         (bpb_bytspersec fat32-in-memory))
  :hints (("goal" :in-theory (enable resize-fat))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    read-reserved-area-correctness-1
    (implies (and (fat32-in-memoryp fat32-in-memory)
                  (stringp str))
             (fat32-in-memoryp
              (mv-nth 0
                      (read-reserved-area fat32-in-memory str))))
    :hints
    (("Goal" :in-theory (disable fat32-in-memoryp))))

  (defun
    string-to-fat32-in-memory
    (fat32-in-memory str)
    (declare
     (xargs
      :guard (and (stringp str)
                  (>= (length str) *initialbytcnt*)
                  (fat32-in-memoryp fat32-in-memory))
      :guard-debug t
      :guard-hints
      (("goal"
        :do-not-induct t
        :in-theory (e/d (cluster-size count-of-clusters)
                        (fat32-in-memoryp read-reserved-area))))
      :stobjs fat32-in-memory))
    (b*
        (((mv fat32-in-memory error-code)
          (read-reserved-area fat32-in-memory str))
         ((unless (equal error-code 0))
          (mv fat32-in-memory error-code))
         (fat-read-size (/ (* (bpb_fatsz32 fat32-in-memory)
                              (bpb_bytspersec fat32-in-memory))
                           4))
         ((unless (integerp fat-read-size))
          (mv fat32-in-memory -1))
         (data-byte-count (* (count-of-clusters fat32-in-memory)
                             (cluster-size fat32-in-memory)))
         ((unless (> data-byte-count 0))
          (mv fat32-in-memory -1))
         (tmp_bytspersec (bpb_bytspersec fat32-in-memory))
         (tmp_init (* tmp_bytspersec
                      (+ (bpb_rsvdseccnt fat32-in-memory)
                         (* (bpb_numfats fat32-in-memory)
                            (bpb_fatsz32 fat32-in-memory)))))
         (fat32-in-memory
          (resize-fat fat-read-size fat32-in-memory))
         ((unless (and (<= fat-read-size *ms-bad-cluster*)
                       (<= (+ (* (bpb_rsvdseccnt fat32-in-memory)
                                 (bpb_bytspersec fat32-in-memory))
                              (* fat-read-size 4))
                           (length str))))
          (mv fat32-in-memory -1))
         (fat32-in-memory
          (update-fat
           fat32-in-memory
           (subseq str
                   (* (bpb_rsvdseccnt fat32-in-memory)
                      (bpb_bytspersec fat32-in-memory))
                   (+ (* (bpb_rsvdseccnt fat32-in-memory)
                         (bpb_bytspersec fat32-in-memory))
                      (* fat-read-size 4)))
           fat-read-size))
         (fat32-in-memory
          (resize-data-region data-byte-count fat32-in-memory))
         ((unless
           (and (<= (data-region-length fat32-in-memory)
                    *ms-max-data-region-size*)
                (>= (length str)
                    (+ tmp_init
                       (data-region-length fat32-in-memory)))))
          (mv fat32-in-memory -1))
         (data-region-string
          (subseq str tmp_init
                  (+ tmp_init
                     (data-region-length fat32-in-memory))))
         (fat32-in-memory
          (update-data-region fat32-in-memory data-region-string
                              (data-region-length fat32-in-memory)
                              0)))
      (mv fat32-in-memory error-code))))

(defun
  slurp-disk-image
  (fat32-in-memory image-path state)
  (declare
   (xargs
    :guard (and (stringp image-path)
                (fat32-in-memoryp fat32-in-memory))
    :guard-hints
    (("goal"
      :do-not-induct t
      :in-theory (disable fat32-in-memoryp read-reserved-area)))
    :stobjs (fat32-in-memory state)))
  (b* ((str (read-file-into-string image-path))
       ((unless (and (stringp str)
                     (>= (length str) *initialbytcnt*)))
        (mv fat32-in-memory -1)))
    (string-to-fat32-in-memory fat32-in-memory str)))

(defun
  get-dir-ent-helper
  (fat32-in-memory data-region-index len ac)
  (declare
   (xargs
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp data-region-index)
                (natp len)
                (<= (+ data-region-index len)
                    (data-region-length fat32-in-memory))
                (unsigned-byte-listp 8 ac))
    :guard-hints (("goal" :in-theory (disable unsigned-byte-p)))
    :stobjs (fat32-in-memory)))
  (if
   (zp len)
   ac
   (let
    ((data-region-index (nfix data-region-index)))
    (get-dir-ent-helper
     fat32-in-memory (+ data-region-index 1)
     (- len 1)
     (cons (data-regioni data-region-index fat32-in-memory)
           ac)))))

(defcong nat-equiv equal
  (get-dir-ent-helper
   fat32-in-memory data-region-index len ac)
  2)

(defthm unsigned-byte-listp-of-revappend
  (equal (unsigned-byte-listp width (revappend x y))
         (and (unsigned-byte-listp width (list-fix x))
              (unsigned-byte-listp width y)))
  :hints (("goal" :induct (revappend x y))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    get-dir-ent-helper-alt
    (equal
     (get-dir-ent-helper fat32-in-memory
                         data-region-index len ac)
     (let ((data-region-index (nfix data-region-index)))
       (revappend
        (subseq-list (nth *data-regioni* fat32-in-memory)
                     data-region-index
                     (+ data-region-index len))
        ac)))
    :hints
    (("goal" :in-theory (e/d (take
                              revappend-removal data-regioni)
                             (take-when-atom)))
     ("subgoal *1/2.4'''" :expand (repeat (+ -1 len) nil))
     ("subgoal *1/2.1'''" :expand (repeat (+ -1 len) nil))
     ))

  (defthm
    get-dir-ent-helper-correctness-1
    (implies
     (and (compliant-fat32-in-memoryp fat32-in-memory)
          (natp data-region-index)
          (<= (+ data-region-index len)
              (data-region-length fat32-in-memory))
          (unsigned-byte-listp 8 ac))
     (and
      (unsigned-byte-listp
       8
       (get-dir-ent-helper fat32-in-memory
                           data-region-index len ac))
      (equal (len (get-dir-ent-helper fat32-in-memory
                                      data-region-index len ac))
             (+ (nfix len) (len ac)))))
    :hints
    (("goal" :do-not-induct t
      :in-theory
      (e/d (unsigned-byte-listp compliant-fat32-in-memoryp
                                data-region-length)
           (unsigned-byte-p data-regioni))))))

(defund get-dir-ent (fat32-in-memory data-region-index)
  (declare
   (xargs
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp data-region-index)
                (<= (+ data-region-index *ms-dir-ent-length*)
                    (data-region-length fat32-in-memory)))
    :stobjs (fat32-in-memory)))
  (rev (get-dir-ent-helper fat32-in-memory data-region-index
                           *ms-dir-ent-length* nil)))

(defthm
  get-dir-ent-correctness-1
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (natp data-region-index)
        (<= (+ data-region-index *ms-dir-ent-length*)
            (data-region-length fat32-in-memory)))
   (and
    (unsigned-byte-listp
     8
     (get-dir-ent fat32-in-memory data-region-index))
    (equal (len (get-dir-ent fat32-in-memory data-region-index))
           *ms-dir-ent-length*)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (data-region-length get-dir-ent unsigned-byte-listp
                             compliant-fat32-in-memoryp)))))

(defund
  get-clusterchain
  (fat32-in-memory masked-current-cluster length)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :measure (nfix length)
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                (fat32-masked-entry-p masked-current-cluster)
                (natp length)
                (>= masked-current-cluster 2)
                (< masked-current-cluster
                   (fat-length fat32-in-memory)))))
  (let
   ((cluster-size (cluster-size fat32-in-memory)))
   (if
    (or (zp length) (zp cluster-size))
    (mv nil (- *eio*))
    (let
     ((masked-next-cluster
       (fat32-entry-mask (fati masked-current-cluster
                               fat32-in-memory))))
     (if
      (< masked-next-cluster *ms-first-data-cluster*)
      (mv (list masked-current-cluster)
          (- *eio*))
      (if
       (or (fat32-is-eof masked-next-cluster)
           (>= masked-next-cluster
               (fat-length fat32-in-memory)))
       (mv (list masked-current-cluster) 0)
       (b*
           (((mv tail-index-list tail-error)
             (get-clusterchain fat32-in-memory masked-next-cluster
                               (nfix (- length cluster-size)))))
         (mv (list* masked-current-cluster tail-index-list)
             tail-error))))))))

(defthm
  get-clusterchain-alt
  (equal (get-clusterchain fat32-in-memory
                           masked-current-cluster length)
         (fat32-build-index-list
          (nth *fati* fat32-in-memory)
          masked-current-cluster
          length (cluster-size fat32-in-memory)))
  :rule-classes :definition
  :hints
  (("goal"
    :in-theory (enable get-clusterchain fati fat-length))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defun
    get-contents-from-clusterchain
    (fat32-in-memory clusterchain file-size)
    (declare
     (xargs
      :stobjs (fat32-in-memory)
      :guard
      (and
       (compliant-fat32-in-memoryp fat32-in-memory)
       (equal (data-region-length fat32-in-memory)
              (* (count-of-clusters fat32-in-memory)
                 (cluster-size fat32-in-memory)))
       (fat32-masked-entry-list-p clusterchain)
       (natp file-size)
       (bounded-nat-listp clusterchain
                          (count-of-clusters fat32-in-memory))
       (lower-bounded-integer-listp
        clusterchain *ms-first-data-cluster*))
      :guard-hints
      (("goal" :in-theory (e/d (lower-bounded-integer-listp)
                               (fat32-in-memoryp))))))
    (if
     (atom clusterchain)
     nil
     (let*
      ((cluster-size (cluster-size fat32-in-memory))
       (masked-current-cluster (car clusterchain))
       (data-region-index (* (nfix (- masked-current-cluster 2))
                             cluster-size)))
      (append
       (rev (get-dir-ent-helper fat32-in-memory data-region-index
                                (min file-size cluster-size) nil))
       (get-contents-from-clusterchain
        fat32-in-memory (cdr clusterchain)
        (nfix (- file-size cluster-size)))))))

  (defun
    get-clusterchain-contents
    (fat32-in-memory masked-current-cluster length)
    (declare
     (xargs
      :stobjs fat32-in-memory
      :measure (nfix length)
      :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                  (equal (data-region-length fat32-in-memory)
                         (* (count-of-clusters fat32-in-memory)
                            (cluster-size fat32-in-memory)))
                  (fat32-masked-entry-p masked-current-cluster)
                  (natp length)
                  (>= masked-current-cluster
                      *ms-first-data-cluster*)
                  (< masked-current-cluster
                     (count-of-clusters fat32-in-memory))
                  (<= (count-of-clusters fat32-in-memory)
                      (fat-length fat32-in-memory)))
      :guard-hints
      (("goal"
        :do-not-induct t
        :in-theory (e/d (fati-when-compliant-fat32-in-memoryp)
                        (fat32-in-memoryp)))
       ("subgoal 1.10'"
        :in-theory (e/d (fat32-in-memoryp)
                        (fat32-entry-p-of-nth))
        :use (:instance fat32-entry-p-of-nth
                        (n masked-current-cluster)
                        (l (nth *fati* fat32-in-memory)))))))
    (b*
        ((cluster-size (cluster-size fat32-in-memory))
         ((unless (and (not (zp length))
                       (not (zp cluster-size))))
          (mv nil (- *eio*)))
         (data-region-index (* (nfix (- masked-current-cluster 2))
                               cluster-size))
         (current-cluster-contents
          (rev (get-dir-ent-helper fat32-in-memory data-region-index
                                   (min length cluster-size)
                                   nil)))
         (masked-next-cluster
          (fat32-entry-mask (fati masked-current-cluster
                                  fat32-in-memory)))
         ((unless (>= masked-next-cluster
                      *ms-first-data-cluster*))
          (mv current-cluster-contents (- *eio*)))
         ((unless (and (not (fat32-is-eof masked-next-cluster))
                       (< masked-next-cluster
                          (count-of-clusters fat32-in-memory))))
          (mv current-cluster-contents 0))
         ((mv tail-character-list tail-error)
          (get-clusterchain-contents
           fat32-in-memory masked-next-cluster
           (nfix (- length cluster-size))))
         ((unless (equal tail-error 0))
          (mv nil (- *eio*))))
      (mv (append current-cluster-contents
                  tail-character-list)
          0))))

(defthm
  get-clusterchain-contents-correctness-2-lemma-1
  (implies
   (not
    (equal
     (mv-nth
      1
      (fat32-build-index-list fa-table masked-current-cluster
                              length cluster-size))
     0))
   (equal
    (mv-nth
     1
     (fat32-build-index-list fa-table masked-current-cluster
                             length cluster-size))
    (- *eio*)))
  :hints (("goal" :in-theory (disable fat32-in-memoryp))))

(defthm
  get-clusterchain-contents-correctness-2
  (implies
   (and (fat32-masked-entry-p masked-current-cluster)
        (>= masked-current-cluster
            *ms-first-data-cluster*)
        (fat32-in-memoryp fat32-in-memory)
        (equal (count-of-clusters fat32-in-memory)
               (fat-length fat32-in-memory)))
   (equal (mv-nth 1
                  (fat32-build-index-list
                   (nth *fati* fat32-in-memory)
                   masked-current-cluster
                   length (cluster-size fat32-in-memory)))
          (mv-nth 1
                  (get-clusterchain-contents
                   fat32-in-memory
                   masked-current-cluster length))))
  :hints (("goal" :in-theory (e/d (cluster-size fat-length fati)
                                  (fat32-in-memoryp)))))

(defthm
  get-clusterchain-contents-correctness-1
  (implies
   (and
    (fat32-masked-entry-p masked-current-cluster)
    (>= masked-current-cluster
        *ms-first-data-cluster*)
    (fat32-in-memoryp fat32-in-memory)
    (equal (count-of-clusters fat32-in-memory)
           (fat-length fat32-in-memory))
    (equal
     (mv-nth
      1
      (get-clusterchain-contents fat32-in-memory
                                 masked-current-cluster length))
     0))
   (equal
    (get-contents-from-clusterchain
     fat32-in-memory
     (mv-nth 0
             (get-clusterchain fat32-in-memory
                               masked-current-cluster length))
     length)
    (mv-nth 0
            (get-clusterchain-contents
             fat32-in-memory
             masked-current-cluster length))))
  :hints
  (("goal" :in-theory (e/d (fat-length fati) (min nth fat32-in-memoryp)))))

;; This whole thing is subject to two criticisms.
;; - The choice not to treat the root directory like other directories is
;; justified on the grounds that it doesn't have a name or a directory
;; entry. However, presumably we'll want to have a function for updating the
;; contents of a directory when a new file is added, and we might have to take
;; the root as a special case.
;; - The name should be stored separately from the rest of the directory entry
;; (or perhaps even redundantly) because not being able to use assoc is a
;; serious issue.

(defun
  fat32-in-memory-to-m1-fs
  (fat32-in-memory dir-contents entry-limit)
  (declare (xargs :measure (acl2-count entry-limit)
                  :verify-guards nil
                  :stobjs (fat32-in-memory)))
  (b*
      (((when (or (zp entry-limit)
                  (equal (nth 0 dir-contents) 0)))
        nil)
       (tail (fat32-in-memory-to-m1-fs
              fat32-in-memory (nthcdr 32 dir-contents)
              (- entry-limit 1)))
       ((when (equal (nth 0 dir-contents) #xe5))
        tail)
       (dir-ent (take 32 dir-contents))
       (first-cluster (combine32u (nth 21 dir-ent)
                                  (nth 20 dir-ent)
                                  (nth 27 dir-ent)
                                  (nth 26 dir-ent)))
       (filename (nats=>string (subseq dir-ent 0 11)))
       (not-right-kind-of-directory-p
        (or (zp (logand (nth 11 dir-ent) (ash 1 4)))
            (equal filename ".          ")
            (equal filename "..         ")))
       (length (if not-right-kind-of-directory-p
                   (dir-ent-file-size dir-ent)
                   (ash 1 21)))
       ((mv contents &)
        (get-clusterchain-contents fat32-in-memory
                                   (fat32-entry-mask first-cluster)
                                   length)))
    (list*
     (cons
      filename
      (if
       not-right-kind-of-directory-p
       (make-m1-file :dir-ent dir-ent
                     :contents (nats=>string contents))
       (make-m1-file
        :dir-ent dir-ent
        :contents
        (fat32-in-memory-to-m1-fs fat32-in-memory
                                  contents (- entry-limit 1)))))
     tail)))

(defthm
  fat32-in-memory-to-m1-fs-correctness-1
  (m1-file-alist-p
   (fat32-in-memory-to-m1-fs fat32-in-memory
                             dir-contents entry-limit))
  :hints (("Goal" :in-theory (disable m1-file-p)) ))

(defund
  stobj-find-n-free-clusters-helper
  (fat32-in-memory n start)
  (declare
   (xargs :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                      (natp n)
                      (natp start))
          :stobjs fat32-in-memory
          :measure (nfix (- (fat-length fat32-in-memory)
                            start))))
  (if
   (or (zp n)
       (mbe :logic (zp (- (fat-length fat32-in-memory) start))
            :exec (>= start (fat-length fat32-in-memory))))
   nil
   (if
    (not (equal (fat32-entry-mask (fati start fat32-in-memory))
                0))
    (stobj-find-n-free-clusters-helper
     fat32-in-memory n (+ start 1))
    (cons
     start
     (stobj-find-n-free-clusters-helper fat32-in-memory (- n 1)
                                        (+ start 1))))))

(defthm
  stobj-find-n-free-clusters-helper-correctness-1
  (implies
   (natp start)
   (equal
    (stobj-find-n-free-clusters-helper fat32-in-memory n start)
    (find-n-free-clusters-helper
     (nthcdr start (nth *fati* fat32-in-memory))
     n start)))
  :hints
  (("goal"
    :in-theory (enable stobj-find-n-free-clusters-helper
                       find-n-free-clusters-helper fat-length fati)
    :induct
    (stobj-find-n-free-clusters-helper fat32-in-memory n start))
   ("subgoal *1/3''"
    :in-theory (disable len-of-nthcdr nth-of-nthcdr)
    :use ((:instance len-of-nthcdr (n start)
                     (l (nth *fati* fat32-in-memory)))
          (:instance nth-of-nthcdr (n 0)
                     (m start)
                     (x (nth *fati* fat32-in-memory)))
          (:instance nthcdr-of-cdr (i start)
                     (x (nth *fati* fat32-in-memory))))
    :expand (find-n-free-clusters-helper
             (nthcdr start (nth *fati* fat32-in-memory))
             n start))
   ("subgoal *1/2'''"
    :in-theory (disable len-of-nthcdr nth-of-nthcdr)
    :use ((:instance len-of-nthcdr (n start)
                     (l (nth *fati* fat32-in-memory)))
          (:instance nth-of-nthcdr (n 0)
                     (m start)
                     (x (nth *fati* fat32-in-memory)))
          (:instance nthcdr-of-cdr (i start)
                     (x (nth *fati* fat32-in-memory))))
    :expand (find-n-free-clusters-helper
             (nthcdr start (nth *fati* fat32-in-memory))
             n start))
   ("subgoal *1/1''"
    :in-theory (disable len-of-nthcdr nth-of-nthcdr)
    :use ((:instance len-of-nthcdr (n start)
                     (l (nth *fati* fat32-in-memory)))
          (:instance nth-of-nthcdr (n 0)
                     (m start)
                     (x (nth *fati* fat32-in-memory)))
          (:instance nthcdr-of-cdr (i start)
                     (x (nth *fati* fat32-in-memory))))
    :expand (find-n-free-clusters-helper
             (nthcdr start (nth *fati* fat32-in-memory))
             n start))))

(defund
  stobj-find-n-free-clusters
  (fat32-in-memory n)
  (declare
   (xargs :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                      (natp n))
          :stobjs fat32-in-memory))
  (stobj-find-n-free-clusters-helper
   fat32-in-memory n *ms-first-data-cluster*))

(defthm
  stobj-find-n-free-clusters-correctness-1
  (equal (stobj-find-n-free-clusters fat32-in-memory n)
         (find-n-free-clusters (nth *fati* fat32-in-memory)
                               n))
  :hints (("goal" :in-theory (enable stobj-find-n-free-clusters
                                     find-n-free-clusters)))
  :rule-classes :definition)

(defthm
  stobj-set-indices-in-fa-table-guard-lemma-1
  (implies (fat32-in-memoryp fat32-in-memory)
           (fat32-entry-list-p (nth *fati* fat32-in-memory))))

(defthm
  stobj-set-indices-in-fa-table-guard-lemma-2
  (implies
   (and (fat32-entry-p entry)
        (fat32-masked-entry-p masked-entry))
   (unsigned-byte-p 32
                    (fat32-update-lower-28 entry masked-entry)))
  :hints
  (("goal"
    :in-theory
    (e/d (fat32-entry-p)
         (fat32-update-lower-28-correctness-1 unsigned-byte-p))
    :use fat32-update-lower-28-correctness-1)))

(defund
  stobj-set-indices-in-fa-table
  (fat32-in-memory index-list value-list)
  (declare
   (xargs :measure (acl2-count index-list)
          :stobjs fat32-in-memory
          :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                      (nat-listp index-list)
                      (fat32-masked-entry-list-p value-list)
                      (equal (len index-list)
                             (len value-list)))
          :guard-debug t
          :guard-hints (("Goal" :in-theory (disable unsigned-byte-p)))))
  (b*
      (((when (atom index-list)) fat32-in-memory)
       (current-index (car index-list))
       ((when
            (or (not (natp current-index))
                (>= current-index (fat-length fat32-in-memory))))
        fat32-in-memory)
       (fat32-in-memory
        (update-fati current-index
                     (fat32-update-lower-28 (fati current-index fat32-in-memory)
                                            (car value-list))
                     fat32-in-memory)))
    (stobj-set-indices-in-fa-table
     fat32-in-memory
     (cdr index-list)
     (cdr value-list))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1-lemma-1
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal (update-nth *fati* (nth *fati* fat32-in-memory)
                      fat32-in-memory)
          fat32-in-memory)))

(defthm
  stobj-set-indices-in-fa-table-correctness-1-lemma-2
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal
    (fat32-in-memoryp (update-nth *fati* val fat32-in-memory))
    (fat32-entry-list-p val))))

(defthm
  stobj-set-indices-in-fa-table-correctness-1
  (implies
   (and (fat32-masked-entry-list-p value-list)
        (equal (len index-list)
               (len value-list))
        (fat32-in-memoryp fat32-in-memory))
   (equal (nth *fati*
               (stobj-set-indices-in-fa-table
                fat32-in-memory index-list value-list))
          (set-indices-in-fa-table (nth *fati* fat32-in-memory)
                                   index-list value-list)))
  :hints
  (("goal"
    :in-theory
    (e/d (set-indices-in-fa-table stobj-set-indices-in-fa-table
                                  fati fat-length update-fati)
         (fat32-in-memoryp))
    :induct t)))

(defthm
  compliant-fat32-in-memoryp-of-stobj-set-indices-in-fa-table
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (fat32-masked-entry-list-p value-list)
                (equal (len index-list)
                       (len value-list)))
           (compliant-fat32-in-memoryp
            (stobj-set-indices-in-fa-table
             fat32-in-memory index-list value-list)))
  :hints
  (("goal"
    :in-theory (enable stobj-set-indices-in-fa-table)
    :induct
    (stobj-set-indices-in-fa-table fat32-in-memory
                                   index-list value-list))))

(defthm
  cluster-size-of-stobj-set-indices-in-fa-table
  (equal
   (cluster-size (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (cluster-size fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  data-region-length-of-update-fati
  (equal (data-region-length (update-fati i v fat32-in-memory))
         (data-region-length fat32-in-memory))
  :hints
  (("goal" :in-theory (enable data-region-length update-fati))))

(defthm
  data-region-length-of-stobj-set-indices-in-fa-table
  (equal
   (data-region-length (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (data-region-length fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  count-of-clusters-of-stobj-set-indices-in-fa-table
  (equal
   (count-of-clusters (stobj-set-indices-in-fa-table
                  fat32-in-memory index-list value-list))
   (count-of-clusters fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defthm
  fat-length-of-stobj-set-indices-in-fa-table
  (equal
   (fat-length (stobj-set-indices-in-fa-table
                fat32-in-memory index-list value-list))
   (fat-length fat32-in-memory))
  :hints
  (("goal" :in-theory (enable stobj-set-indices-in-fa-table))))

(defund
  dir-ent-set-first-cluster-file-size
    (dir-ent first-cluster file-size)
  (declare (xargs :guard (and (dir-ent-p dir-ent)
                              (fat32-masked-entry-p first-cluster)
                              (unsigned-byte-p 32 file-size))))
  (let
      ((dir-ent (dir-ent-fix dir-ent))
       (first-cluster (fat32-masked-entry-fix first-cluster))
       (file-size (if (not (unsigned-byte-p 32 file-size)) 0 file-size)))
   (append
    (subseq dir-ent 0 20)
    (list* (logtail 16 (loghead 24 first-cluster))
           (logtail 24 first-cluster)
           (append (subseq dir-ent 22 26)
                   (list (loghead 8 first-cluster)
                         (logtail 8 (loghead 16 first-cluster))
                         (loghead 8 file-size)
                         (logtail 8 (loghead 16 file-size))
                         (logtail 16 (loghead 24 file-size))
                         (logtail 24 file-size)))))))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (defthm dir-ent-set-first-cluster-file-size-correctness-1
    (dir-ent-p (dir-ent-set-first-cluster-file-size dir-ent first-cluster file-size))
    :hints (("goal" :in-theory (e/d (dir-ent-set-first-cluster-file-size
                                     fat32-masked-entry-fix fat32-masked-entry-p)
                                    (loghead logtail))))))

(defund
  make-clusters (text cluster-size)
  (declare (xargs :guard (and (unsigned-byte-listp 8 text)
                              (natp cluster-size))
                  :measure (len text)
                  :guard-debug t))
  (if
   (or (atom text) (zp cluster-size))
   nil
   (list* (append (take (min cluster-size (len text))
                        text)
                  (make-list (nfix (- cluster-size (len text)))
                             :initial-element 0))
          (make-clusters (nthcdr cluster-size text)
                         cluster-size))))

(defthm
  make-clusters-correctness-1
  (iff (consp (make-clusters text cluster-size))
       (and (consp text)
            (not (zp cluster-size))))
  :hints (("goal" :in-theory (enable make-clusters)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (iff (equal (len (make-clusters text cluster-size))
                0)
         (or (atom text) (zp cluster-size)))
    :hints
    (("goal"
      :expand (len (make-clusters text cluster-size)))))))

(defun stobj-set-cluster (cluster fat32-in-memory end-index)
  (declare (xargs :stobjs fat32-in-memory
                  :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                              (integerp end-index)
                              (>= end-index (len cluster))
                              (<= end-index (data-region-length
                                             fat32-in-memory))
                              (unsigned-byte-listp 8 cluster))
                  :guard-hints (("Goal" :in-theory (disable fat32-in-memoryp)) )))
  (b*
      (((unless (consp cluster))
        fat32-in-memory)
       (fat32-in-memory
        (update-data-regioni (- end-index (len cluster)) (car cluster)
                             fat32-in-memory)))
    (stobj-set-cluster (cdr cluster) fat32-in-memory end-index)))

(defun cluster-listp (l fat32-in-memory)
  (declare (xargs :stobjs fat32-in-memory))
  (if
      (atom l)
      (equal l nil)
    (and (unsigned-byte-listp 8 (car l))
         (equal (len (car l))
                (cluster-size fat32-in-memory))
         (cluster-listp (cdr l) fat32-in-memory))))

(defthm
  cluster-listp-of-make-clusters
  (implies
   (and (unsigned-byte-listp 8 text)
        (equal cluster-size (cluster-size fat32-in-memory)))
   (cluster-listp
    (make-clusters text cluster-size)
    fat32-in-memory))
  :hints
  (("goal" :in-theory (enable cluster-listp make-clusters make-list-ac-removal))))

(defthm
  bpb_bytspersec-of-update-data-regioni
  (equal
   (bpb_bytspersec (update-data-regioni i v fat32-in-memory))
   (bpb_bytspersec fat32-in-memory))
  :hints (("goal" :in-theory (enable update-data-regioni))))

(defthm
  bpb_secperclus-of-update-data-regioni
  (equal
   (bpb_secperclus (update-data-regioni i v fat32-in-memory))
   (bpb_secperclus fat32-in-memory))
  :hints (("goal" :in-theory (enable update-data-regioni))))

(defthm
  bpb_totsec32-of-update-data-regioni
  (equal
   (bpb_totsec32 (update-data-regioni i v fat32-in-memory))
   (bpb_totsec32 fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni bpb_totsec32))))

(defthm
  fat-length-of-update-data-regioni
  (equal
   (fat-length (update-data-regioni i v fat32-in-memory))
   (fat-length fat32-in-memory))
  :hints (("goal" :in-theory (enable update-data-regioni fat-length))))

(defthm
  cluster-size-of-stobj-set-cluster
  (equal
   (cluster-size
    (stobj-set-cluster cluster fat32-in-memory end-index))
   (cluster-size fat32-in-memory))
  :hints (("goal" :in-theory (enable cluster-size))))

(defthm
  count-of-clusters-of-stobj-set-cluster
  (equal
   (count-of-clusters
    (stobj-set-cluster cluster fat32-in-memory end-index))
   (count-of-clusters fat32-in-memory))
  :hints
  (("goal"
    :in-theory
    (e/d
     (count-of-clusters update-data-regioni bpb_bytspersec
                        bpb_secperclus count-of-clusters
                        bpb_numfats bpb_fatsz32 bpb_rsvdseccnt
                        bpb_secperclus bpb_totsec32)
     (floor)))))

(defthm
  cluster-listp-of-stobj-set-cluster
  (equal
   (cluster-listp
    l
    (stobj-set-cluster cluster fat32-in-memory end-index))
   (cluster-listp l fat32-in-memory))
  :hints (("goal" :induct (cluster-listp l fat32-in-memory))))

(defthm
  compliant-fat32-in-memoryp-of-stobj-set-cluster
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (unsigned-byte-listp 8 cluster)
        (<= end-index
            (data-region-length fat32-in-memory)))
   (compliant-fat32-in-memoryp
    (stobj-set-cluster cluster fat32-in-memory end-index)))
  :hints
  (("subgoal *1/3''" :in-theory (enable data-region-length
                                        update-data-regioni))))

(defthm
  data-region-length-of-stobj-set-cluster
  (implies
   (and (integerp end-index)
        (>= end-index (len cluster))
        (<= end-index
            (data-region-length fat32-in-memory)))
   (equal
    (data-region-length
     (stobj-set-cluster cluster fat32-in-memory end-index))
    (data-region-length fat32-in-memory))))

(defthm
  fat-length-of-stobj-set-cluster
  (equal
   (fat-length
    (stobj-set-cluster cluster fat32-in-memory end-index))
   (fat-length fat32-in-memory)))

(defun
    stobj-set-clusters
    (cluster-list index-list fat32-in-memory)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard
    (and (compliant-fat32-in-memoryp fat32-in-memory)
         (lower-bounded-integer-listp
          index-list *ms-first-data-cluster*)
         (cluster-listp cluster-list fat32-in-memory)
         (equal (len index-list)
                (len cluster-list))
         (equal (data-region-length fat32-in-memory)
                (* (count-of-clusters fat32-in-memory)
                   (cluster-size fat32-in-memory))))
    :verify-guards nil))
  (b*
      (((unless (consp cluster-list))
        (mv fat32-in-memory nil))
       ((mv fat32-in-memory tail-list)
        (stobj-set-clusters (cdr cluster-list)
                            (cdr index-list)
                            fat32-in-memory))
       ((unless (< (car index-list)
                   (+ *ms-first-data-cluster*
                      (count-of-clusters fat32-in-memory))))
        (mv fat32-in-memory tail-list))
       (fat32-in-memory
        (stobj-set-cluster (car cluster-list)
                           fat32-in-memory
                           (* (- (car index-list) 1)
                              (cluster-size fat32-in-memory)))))
    (mv fat32-in-memory (list* (car index-list) tail-list))))

(defthm
  cluster-size-of-stobj-set-clusters
  (equal
   (cluster-size
    (mv-nth 0
            (stobj-set-clusters cluster-list
                                index-list fat32-in-memory)))
   (cluster-size fat32-in-memory)))

(defthm
  count-of-clusters-of-stobj-set-clusters
  (equal
   (count-of-clusters
    (mv-nth 0
            (stobj-set-clusters cluster-list
                                index-list fat32-in-memory)))
   (count-of-clusters fat32-in-memory)))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    data-region-length-of-stobj-set-clusters
    (implies
     (and
      (lower-bounded-integer-listp
       index-list *ms-first-data-cluster*)
      (cluster-listp cluster-list fat32-in-memory)
      (equal (len index-list)
             (len cluster-list))
      (equal (data-region-length fat32-in-memory)
             (* (count-of-clusters fat32-in-memory)
                (cluster-size fat32-in-memory))))
     (equal
      (data-region-length
       (mv-nth 0
               (stobj-set-clusters cluster-list
                                   index-list fat32-in-memory)))
      (data-region-length fat32-in-memory)))
    :hints
    (("goal"
      :induct (stobj-set-clusters cluster-list
                                  index-list fat32-in-memory))
     ("subgoal *1/2'"
      :expand (lower-bounded-integer-listp
               index-list *ms-first-data-cluster*))
     ("subgoal *1/1'"
      :expand (lower-bounded-integer-listp
               index-list *ms-first-data-cluster*))))

  (defthm
    compliant-fat32-in-memoryp-of-stobj-set-clusters
    (implies
     (and (compliant-fat32-in-memoryp fat32-in-memory)
          (lower-bounded-integer-listp
           index-list *ms-first-data-cluster*)
          (cluster-listp cluster-list fat32-in-memory)
          (equal (len cluster-list)
                 (len index-list))
          (equal (data-region-length fat32-in-memory)
                 (* (count-of-clusters fat32-in-memory)
                    (cluster-size fat32-in-memory))))
     (compliant-fat32-in-memoryp
      (mv-nth 0
              (stobj-set-clusters cluster-list
                                  index-list fat32-in-memory))))
    :hints
    (("goal"
      :induct
      (stobj-set-clusters cluster-list index-list fat32-in-memory)
      :in-theory (enable lower-bounded-integer-listp))
     ("subgoal *1/1'"
      :in-theory
      (disable compliant-fat32-in-memoryp-of-stobj-set-cluster)
      :use
      (:instance
       compliant-fat32-in-memoryp-of-stobj-set-cluster
       (cluster (car cluster-list))
       (fat32-in-memory
        (mv-nth 0
                (stobj-set-clusters (cdr cluster-list)
                                    (cdr index-list)
                                    fat32-in-memory)))
       (end-index (+ (* -1 (cluster-size fat32-in-memory))
                     (* (car index-list)
                        (cluster-size fat32-in-memory))))))
     ("subgoal *1/1'''"
      :expand (lower-bounded-integer-listp index-list 2))))

  (verify-guards
    stobj-set-clusters
    :hints
    (("goal" :in-theory (e/d (lower-bounded-integer-listp)
                             (fat32-in-memoryp
                              ;; wisdom from accumulated-persistence
                              ;; not enough - this really needs to be sped up
                              (:DEFINITION ACL2-NUMBER-LISTP)
                              (:DEFINITION RATIONAL-LISTP)
                              (:DEFINITION INTEGER-LISTP)
                              (:REWRITE
                               RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP)
                              (:REWRITE
                               ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP)
                              (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP)))
      :induct (stobj-set-clusters
               cluster-list index-list fat32-in-memory)))
    :guard-debug t))

(defthm
  bounded-nat-listp-of-stobj-set-clusters
  (implies
   (and (lower-bounded-integer-listp
         index-list *ms-first-data-cluster*)
        (equal (len index-list)
               (len cluster-list)))
   (bounded-nat-listp
    (mv-nth 1
            (stobj-set-clusters cluster-list
                                index-list fat32-in-memory))
    (+ *ms-first-data-cluster*
       (count-of-clusters fat32-in-memory))))
  :hints
  (("goal" :in-theory (enable lower-bounded-integer-listp))))

(defthm
  fat32-masked-entry-list-p-of-stobj-set-clusters
  (implies
   (and (lower-bounded-integer-listp
         index-list *ms-first-data-cluster*)
        (equal (len index-list)
               (len cluster-list))
        (<= (+ *ms-first-data-cluster*
               (count-of-clusters fat32-in-memory))
            *ms-bad-cluster*))
   (fat32-masked-entry-list-p
    (mv-nth 1
            (stobj-set-clusters cluster-list
                                index-list fat32-in-memory))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (lower-bounded-integer-listp
           index-list *ms-first-data-cluster*)
          (equal (len index-list)
                 (len cluster-list))
          (<= (+ *ms-first-data-cluster*
                 (count-of-clusters fat32-in-memory))
              *ms-bad-cluster*))
     (let
      ((l
        (mv-nth
         1
         (stobj-set-clusters cluster-list
                             index-list fat32-in-memory))))
      (implies (consp l)
               (and (fat32-masked-entry-list-p (cdr l))
                    (fat32-masked-entry-p (car l))))))))
  :hints
  (("goal"
    :use
    ((:instance
      fat32-masked-entry-list-p-alt
      (x (mv-nth
          1
          (stobj-set-clusters cluster-list
                              index-list fat32-in-memory))))
     (:instance
      bounded-nat-listp-correctness-5
      (l
       (mv-nth 1
               (stobj-set-clusters cluster-list
                                   index-list fat32-in-memory)))
      (x (+ (count-of-clusters fat32-in-memory)
            *ms-first-data-cluster*))
      (y *expt-2-28*))))))

(defthm
  fat-length-of-stobj-set-clusters
  (equal
   (fat-length
    (mv-nth 0
            (stobj-set-clusters cluster-list
                                index-list fat32-in-memory)))
   (fat-length fat32-in-memory)))

(defund
  place-contents
  (fat32-in-memory dir-ent contents file-length)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                (dir-ent-p dir-ent)
                (unsigned-byte-p 32 file-length)
                (unsigned-byte-listp 8 contents)
                (<= (fat-length fat32-in-memory)
                    *ms-bad-cluster*)
                (>= (fat-length fat32-in-memory)
                    *ms-first-data-cluster*)
                (<= (+ *ms-first-data-cluster*
                       (count-of-clusters fat32-in-memory))
                    *ms-bad-cluster*)
                (equal (data-region-length fat32-in-memory)
                       (* (count-of-clusters fat32-in-memory)
                          (cluster-size fat32-in-memory))))
    :guard-debug t
    :guard-hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d (fat-length)
           (fat32-in-memoryp
            true-listp-when-fat32-masked-entry-list-p))
      :use
      (:instance
       true-listp-when-fat32-masked-entry-list-p
       (x
        (cdr
         (mv-nth
          1
          (stobj-set-clusters
           (make-clusters
            contents (cluster-size fat32-in-memory))
           (find-n-free-clusters
            (nth *fati* fat32-in-memory)
            (len
             (make-clusters contents
                            (cluster-size fat32-in-memory))))
           fat32-in-memory)))))))))
  (b*
      ((dir-ent (dir-ent-fix dir-ent))
       (cluster-size (cluster-size fat32-in-memory))
       (clusters (make-clusters contents cluster-size))
       (indices (stobj-find-n-free-clusters
                 fat32-in-memory (len clusters)))
       ((unless (equal (len indices) (len clusters)))
        (mv fat32-in-memory dir-ent))
       ((mv fat32-in-memory indices)
        (stobj-set-clusters clusters indices fat32-in-memory))
       ((mv fat32-in-memory dir-ent)
        (if
         (consp indices)
         (let
          ((fat32-in-memory
            (stobj-set-indices-in-fa-table
             fat32-in-memory indices
             (binary-append (cdr indices)
                            (list *ms-end-of-clusterchain*)))))
          (mv fat32-in-memory
              (dir-ent-set-first-cluster-file-size
               dir-ent (car indices)
               file-length)))
         (mv fat32-in-memory
             (dir-ent-set-first-cluster-file-size
              dir-ent 0 file-length)))))
    (mv fat32-in-memory dir-ent)))

(defthm
  compliant-fat32-in-memoryp-of-place-contents
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (unsigned-byte-listp 8 contents)
        (natp file-length)
        (equal (data-region-length fat32-in-memory)
               (* (cluster-size fat32-in-memory)
                  (count-of-clusters fat32-in-memory)))
        (<= (+ *ms-first-data-cluster*
               (count-of-clusters fat32-in-memory))
            *ms-bad-cluster*))
   (compliant-fat32-in-memoryp
    (mv-nth 0
            (place-contents fat32-in-memory
                            dir-ent contents file-length))))
  :hints
  (("goal"
    :in-theory (e/d (place-contents)
                    (true-listp-when-fat32-masked-entry-list-p))
    :use
    (:instance
     true-listp-when-fat32-masked-entry-list-p
     (x
      (cdr
       (mv-nth
        1
        (stobj-set-clusters
         (make-clusters contents (cluster-size fat32-in-memory))
         (find-n-free-clusters
          (nth *fati* fat32-in-memory)
          (len (make-clusters contents
                              (cluster-size fat32-in-memory))))
         fat32-in-memory))))))))

(defthm
  cluster-size-of-place-contents
  (equal
   (cluster-size
    (mv-nth 0
            (place-contents fat32-in-memory
                            dir-ent contents file-length)))
   (cluster-size fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  count-of-clusters-of-place-contents
  (equal
   (count-of-clusters
    (mv-nth 0
            (place-contents fat32-in-memory
                            dir-ent contents file-length)))
   (count-of-clusters fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  data-region-length-of-place-contents
  (implies
   (and (unsigned-byte-listp 8 contents)
        (equal (data-region-length fat32-in-memory)
               (* (cluster-size fat32-in-memory)
                  (count-of-clusters fat32-in-memory))))
   (equal
    (data-region-length
     (mv-nth 0
             (place-contents fat32-in-memory
                             dir-ent contents file-length)))
    (data-region-length fat32-in-memory)))
  :hints (("goal" :in-theory (enable place-contents))))

(defthm
  dir-ent-p-of-place-contents
  (dir-ent-p
   (mv-nth 1
           (place-contents fat32-in-memory
                           dir-ent contents file-length)))
  :hints
  (("goal" :in-theory (e/d (place-contents) (dir-ent-p))))
  :rule-classes
  ((:rewrite
    :corollary
    (unsigned-byte-listp
     8
     (mv-nth 1
             (place-contents fat32-in-memory
                             dir-ent contents file-length))))))

(defthm
  fat-length-of-place-contents
  (equal
   (fat-length
    (mv-nth 0
            (place-contents fat32-in-memory
                            dir-ent contents file-length)))
   (fat-length fat32-in-memory))
  :hints (("goal" :in-theory (enable place-contents))))

;; Gotta return a list of directory entries to join up later when constructing
;; the containing directory.
(defun
  m1-fs-to-fat32-in-memory-helper
  (fat32-in-memory fs)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                (m1-file-alist-p fs)
                (equal (data-region-length fat32-in-memory)
                       (* (cluster-size fat32-in-memory)
                          (count-of-clusters fat32-in-memory)))
                (<= (+ *ms-first-data-cluster*
                       (count-of-clusters fat32-in-memory))
                    *ms-bad-cluster*)
                (>= (fat-length fat32-in-memory)
                    *ms-first-data-cluster*)
                (<= (fat-length fat32-in-memory)
                    *ms-bad-cluster*))
    :hints (("goal" :in-theory (e/d (m1-file->contents)
                                    (fat32-in-memoryp))))
    :verify-guards nil))
  (b*
      ;; this clause is there simply because we didn't require all files in
      ;; subdirectories to fall into the regular file and directory file
      ;; categories.
      (((unless (consp fs))
        (mv fat32-in-memory nil))
       ((mv fat32-in-memory tail-list)
        (m1-fs-to-fat32-in-memory-helper fat32-in-memory (cdr fs)))
       (head (car fs))
       (dir-ent (m1-file->dir-ent (cdr head)))
       ((unless
         (or (and (m1-regular-file-p (cdr head))
                  (unsigned-byte-p
                   32
                   (length (m1-file->contents (cdr head)))))
             (m1-directory-file-p (cdr head))))
        (mv fat32-in-memory tail-list))
       ((mv fat32-in-memory dir-ent)
        (if
         (m1-regular-file-p (cdr head))
         (b*
             ((contents (string=>nats (m1-file->contents (cdr head))))
              (file-length (length contents)))
           (place-contents fat32-in-memory
                           dir-ent contents file-length))
         (b* ((contents (m1-file->contents (cdr head)))
              (file-length 0) ;; per the specification
              ((mv fat32-in-memory unflattened-contents)
               (m1-fs-to-fat32-in-memory-helper fat32-in-memory contents))
              (contents (flatten unflattened-contents)))
           (place-contents fat32-in-memory
                           dir-ent contents file-length)))))
    (mv fat32-in-memory
        (list* dir-ent tail-list))))

(defthm
  cluster-size-of-m1-fs-to-fat32-in-memory-helper
  (equal
   (cluster-size
    (mv-nth 0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs)))
   (cluster-size fat32-in-memory)))

(defthm
  count-of-clusters-of-m1-fs-to-fat32-in-memory-helper
  (equal
   (count-of-clusters
    (mv-nth 0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs)))
   (count-of-clusters fat32-in-memory)))

(defthm
  unsigned-byte-listp-of-m1-fs-to-fat32-in-memory-helper
  (unsigned-byte-listp
   8
   (flatten
    (mv-nth 1
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs)))))

(defthm
  data-region-length-of-m1-fs-to-fat32-in-memory-helper
  (implies
   ;; Possibly this hypothesis can be removed...
   (equal (data-region-length fat32-in-memory)
          (* (cluster-size fat32-in-memory)
             (count-of-clusters fat32-in-memory)))
   (equal
    (data-region-length
     (mv-nth 0
             (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs)))
    (data-region-length fat32-in-memory))))

(defthm
  compliant-fat32-in-memoryp-of-m1-fs-to-fat32-in-memory-helper
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (equal (data-region-length fat32-in-memory)
               (* (cluster-size fat32-in-memory)
                  (count-of-clusters fat32-in-memory)))
        (<= (+ *ms-first-data-cluster*
               (count-of-clusters fat32-in-memory))
            *ms-bad-cluster*))
   (compliant-fat32-in-memoryp
    (mv-nth 0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs)))))

(defthm
  fat-length-of-m1-fs-to-fat32-in-memory-helper
  (equal
   (fat-length
    (mv-nth 0
            (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs)))
   (fat-length fat32-in-memory)))

(verify-guards m1-fs-to-fat32-in-memory-helper :guard-debug t)

(defun
  m1-fs-to-fat32-in-memory
  (fat32-in-memory fs)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                (m1-file-alist-p fs)
                (equal (data-region-length fat32-in-memory)
                       (* (cluster-size fat32-in-memory)
                          (count-of-clusters fat32-in-memory)))
                (<= (+ *ms-first-data-cluster*
                       (count-of-clusters fat32-in-memory))
                    *ms-bad-cluster*)
                (>= (fat-length fat32-in-memory)
                    *ms-first-data-cluster*)
                (<= (fat-length fat32-in-memory)
                    *ms-bad-cluster*))
    :guard-debug t
    :guard-hints
    (("goal" :in-theory (disable fat32-in-memoryp)
      :do-not-induct t)
     ("subgoal 2"
      :in-theory
      (e/d (lower-bounded-integer-listp)
           (true-listp-when-fat32-masked-entry-list-p))
      :use
      (:instance
       true-listp-when-fat32-masked-entry-list-p
       (x
        (cdr
         (mv-nth
          1
          (stobj-set-clusters
           (make-clusters
            (flatten
             (mv-nth
              1
              (m1-fs-to-fat32-in-memory-helper
               (stobj-set-indices-in-fa-table
                fat32-in-memory
                (remove-equal
                 (bpb_rootclus fat32-in-memory)
                 (generate-index-list
                  2 (+ -2 (fat-length fat32-in-memory))))
                (make-list-ac
                 (len
                  (remove-equal
                   (bpb_rootclus fat32-in-memory)
                   (generate-index-list
                    2 (+ -2 (fat-length fat32-in-memory)))))
                 0 nil))
               fs)))
            (cluster-size fat32-in-memory))
           (cons
            (bpb_rootclus fat32-in-memory)
            (find-n-free-clusters
             (nth
              *fati*
              (mv-nth
               0
               (m1-fs-to-fat32-in-memory-helper
                (stobj-set-indices-in-fa-table
                 fat32-in-memory
                 (remove-equal
                  (bpb_rootclus fat32-in-memory)
                  (generate-index-list
                   2 (+ -2 (fat-length fat32-in-memory))))
                 (make-list-ac
                  (len
                   (remove-equal
                    (bpb_rootclus fat32-in-memory)
                    (generate-index-list
                     2 (+ -2 (fat-length fat32-in-memory)))))
                  0 nil))
                fs)))
             (+
              -1
              (len
               (make-clusters
                (flatten
                 (mv-nth
                  1
                  (m1-fs-to-fat32-in-memory-helper
                   (stobj-set-indices-in-fa-table
                    fat32-in-memory
                    (remove-equal
                     (bpb_rootclus fat32-in-memory)
                     (generate-index-list
                      2 (+ -2 (fat-length fat32-in-memory))))
                    (make-list-ac
                     (len
                      (remove-equal
                       (bpb_rootclus fat32-in-memory)
                       (generate-index-list
                        2
                        (+ -2 (fat-length fat32-in-memory)))))
                     0 nil))
                   fs)))
                (cluster-size fat32-in-memory))))))
           (mv-nth
            0
            (m1-fs-to-fat32-in-memory-helper
             (stobj-set-indices-in-fa-table
              fat32-in-memory
              (remove-equal
               (bpb_rootclus fat32-in-memory)
               (generate-index-list
                2 (+ -2 (fat-length fat32-in-memory))))
              (make-list-ac
               (len
                (remove-equal
                 (bpb_rootclus fat32-in-memory)
                 (generate-index-list
                  2 (+ -2 (fat-length fat32-in-memory)))))
               0 nil))
             fs)))))))))))
  (b*
      ((rootclus (bpb_rootclus fat32-in-memory))
       (cluster-size (cluster-size fat32-in-memory))
       (index-list-to-clear
        (remove
         rootclus
         (generate-index-list *ms-first-data-cluster*
                              (- (fat-length fat32-in-memory)
                                 *ms-first-data-cluster*))))
       (fat32-in-memory (stobj-set-indices-in-fa-table
                         fat32-in-memory index-list-to-clear
                         (make-list (len index-list-to-clear)
                                    :initial-element 0)))
       ((mv fat32-in-memory dir-ent-list)
        (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs))
       (contents (flatten dir-ent-list))
       (clusters (make-clusters contents cluster-size))
       (indices (list* rootclus
                       (stobj-find-n-free-clusters
                        fat32-in-memory
                        (nfix (- (len clusters) 1)))))
       ((unless (equal (len indices) (len clusters)))
        fat32-in-memory)
       ((mv fat32-in-memory indices)
        (stobj-set-clusters clusters indices fat32-in-memory))
       (fat32-in-memory
        (if
         (atom indices)
         fat32-in-memory
         (stobj-set-indices-in-fa-table
          fat32-in-memory indices
          (binary-append (cdr indices)
                         (list *ms-end-of-clusterchain*))))))
    fat32-in-memory))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (defun
    stobj-fa-table-to-string
    (fat32-in-memory length)
    (declare
     (xargs
      :stobjs fat32-in-memory
      :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                  (natp length)
                  (<= length (fat-length fat32-in-memory)))
      :guard-hints
      (("goal"
        :in-theory
        (e/d
         (fat32-entry-p)
         (fat32-in-memoryp unsigned-byte-p loghead logtail
                           fati-when-compliant-fat32-in-memoryp))
        :use (:instance fati-when-compliant-fat32-in-memoryp
                        (i (+ -1 length)))))))
    (if
     (zp length)
     ""
     (concatenate
      'string
      (stobj-fa-table-to-string fat32-in-memory (- length 1))
      (let ((current (fati (- length 1) fat32-in-memory)))
        (nats=>string (list
                       (loghead 8             current )
                       (loghead 8 (logtail  8 current))
                       (loghead 8 (logtail 16 current))
                                  (logtail 24 current) )))))))

(defthm
  reserved-area-string-guard-lemma-1
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp i)
                (< i (bs_vollab-length fat32-in-memory)))
           (and (integerp (bs_vollabi i fat32-in-memory))
                (<= 0 (bs_vollabi i fat32-in-memory))
                (< (bs_vollabi i fat32-in-memory) 256)))
  :rule-classes
  ((:rewrite
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (bs_vollab-length fat32-in-memory)))
                        (integerp (bs_vollabi i fat32-in-memory))))
   (:linear
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (bs_vollab-length fat32-in-memory)))
                        (and (<= 0 (bs_vollabi i fat32-in-memory))
                             (< (bs_vollabi i fat32-in-memory)
                                256)))))
  :hints
  (("goal"
    :in-theory
    (e/d (compliant-fat32-in-memoryp)
         (update-bs_vollab-correctness-4 bs_vollabi fat32-in-memoryp))
    :use update-bs_vollab-correctness-4)))

(defthm
  reserved-area-string-guard-lemma-2
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp i)
                (< i (bs_jmpboot-length fat32-in-memory)))
           (and (integerp (bs_jmpbooti i fat32-in-memory))
                (<= 0 (bs_jmpbooti i fat32-in-memory))
                (< (bs_jmpbooti i fat32-in-memory) 256)))
  :rule-classes
  ((:rewrite
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (bs_jmpboot-length fat32-in-memory)))
                        (integerp (bs_jmpbooti i fat32-in-memory))))
   (:linear
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (bs_jmpboot-length fat32-in-memory)))
                        (and (<= 0 (bs_jmpbooti i fat32-in-memory))
                             (< (bs_jmpbooti i fat32-in-memory)
                                256)))))
  :hints
  (("goal"
    :in-theory
    (e/d (compliant-fat32-in-memoryp)
         (update-bs_jmpboot-correctness-4 bs_jmpbooti fat32-in-memoryp))
    :use update-bs_jmpboot-correctness-4)))

(defthm
  reserved-area-string-guard-lemma-3
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp i)
                (< i (bs_oemname-length fat32-in-memory)))
           (and (integerp (bs_oemnamei i fat32-in-memory))
                (<= 0 (bs_oemnamei i fat32-in-memory))
                (< (bs_oemnamei i fat32-in-memory) 256)))
  :rule-classes
  ((:rewrite
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (bs_oemname-length fat32-in-memory)))
                        (integerp (bs_oemnamei i fat32-in-memory))))
   (:linear
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (bs_oemname-length fat32-in-memory)))
                        (and (<= 0 (bs_oemnamei i fat32-in-memory))
                             (< (bs_oemnamei i fat32-in-memory)
                                256)))))
  :hints
  (("goal"
    :in-theory
    (e/d (compliant-fat32-in-memoryp)
         (update-bs_oemname-correctness-4 bs_oemnamei fat32-in-memoryp))
    :use update-bs_oemname-correctness-4)))

(defthm
  reserved-area-string-guard-lemma-4
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp i)
                (< i (bs_filsystype-length fat32-in-memory)))
           (and (integerp (bs_filsystypei i fat32-in-memory))
                (<= 0 (bs_filsystypei i fat32-in-memory))
                (< (bs_filsystypei i fat32-in-memory) 256)))
  :rule-classes
  ((:rewrite
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (bs_filsystype-length fat32-in-memory)))
                        (integerp (bs_filsystypei i fat32-in-memory))))
   (:linear
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (bs_filsystype-length fat32-in-memory)))
                        (and (<= 0 (bs_filsystypei i fat32-in-memory))
                             (< (bs_filsystypei i fat32-in-memory)
                                256)))))
  :hints
  (("goal"
    :in-theory
    (e/d (compliant-fat32-in-memoryp)
         (update-bs_filsystype-correctness-4 bs_filsystypei fat32-in-memoryp))
    :use update-bs_filsystype-correctness-4)))

(defthm
  reserved-area-string-guard-lemma-5
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp i)
                (< i (bpb_reserved-length fat32-in-memory)))
           (and (integerp (bpb_reservedi i fat32-in-memory))
                (<= 0 (bpb_reservedi i fat32-in-memory))
                (< (bpb_reservedi i fat32-in-memory) 256)))
  :rule-classes
  ((:rewrite
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (bpb_reserved-length fat32-in-memory)))
                        (integerp (bpb_reservedi i fat32-in-memory))))
   (:linear
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (bpb_reserved-length fat32-in-memory)))
                        (and (<= 0 (bpb_reservedi i fat32-in-memory))
                             (< (bpb_reservedi i fat32-in-memory)
                                256)))))
  :hints
  (("goal"
    :in-theory
    (e/d (compliant-fat32-in-memoryp)
         (update-bpb_reserved-correctness-4 bpb_reservedi fat32-in-memoryp))
    :use update-bpb_reserved-correctness-4)))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (local
   (defthm
     reserved-area-string-guard-lemma-6
     (implies (and (logtail-guard size i)
                   (unsigned-byte-p (+ size 8) i))
              (and (integerp (logtail size i))
                   (<= 0 (logtail size i))
                   (< (logtail size i) 256)))
     :rule-classes
     ((:rewrite
       :corollary
       (implies (and (logtail-guard size i)
                     (unsigned-byte-p (+ size 8) i))
                (integerp (logtail size i))))
      (:linear
       :corollary
       (implies (and (logtail-guard size i)
                     (unsigned-byte-p (+ size 8) i))
                (and (<= 0 (logtail size i))
                     (< (logtail size i) 256)))))
     :hints
     (("goal" :in-theory (disable logtail-unsigned-byte-p)
       :use (:instance logtail-unsigned-byte-p (size1 8))))))

  (local
   (in-theory (enable bpb_secperclus bpb_fatsz32 bpb_rsvdseccnt
                      bpb_numfats bpb_bytspersec bpb_rootclus bpb_fsinfo
                      bpb_bkbootsec bs_drvnum bs_reserved1 bs_bootsig
                      bpb_media bpb_fsver_major bpb_fsver_major bpb_fatsz16
                      bpb_secpertrk bpb_numheads bpb_rootentcnt
                      bpb_extflags bpb_hiddsec bpb_totsec32 bpb_fatsz32
                      bpb_rootentcnt bpb_totsec16 bs_volid
                      update-bpb_secperclus update-bpb_rsvdseccnt
                      update-bpb_bytspersec update-bpb_numfats
                      update-bpb_rootclus update-bpb_fsinfo update-bpb_bkbootsec
                      update-bs_drvnum update-bs_reserved1 update-bs_bootsig
                      update-bpb_media update-bpb_fsver_minor
                      update-bpb_fsver_major update-bpb_fatsz16
                      update-bpb_secpertrk update-bpb_numheads
                      update-bpb_extflags update-bpb_hiddsec update-bpb_totsec32
                      update-bpb_fatsz32 update-bpb_rootentcnt
                      update-bpb_totsec16 update-bs_volid)))

  (defund reserved-area-string (fat32-in-memory)
    (declare (xargs :stobjs fat32-in-memory
                    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                                (<= 90
                                    (* (BPB_BYTSPERSEC FAT32-IN-MEMORY)
                                       (BPB_RSVDSECCNT FAT32-IN-MEMORY))))
                    :guard-debug t
                    :guard-hints (("Goal"
                                   :do-not-induct t
                                   :in-theory (disable loghead logtail
                                                       bs_vollabi
                                                       bs_jmpbooti
                                                       bs_oemnamei
                                                       bs_filsystypei
                                                       bpb_reservedi)))))
    (coerce
     (append
      ;; initial bytes
      (list (code-char (bs_jmpbooti 0 fat32-in-memory))
            (code-char (bs_jmpbooti 1 fat32-in-memory))
            (code-char (bs_jmpbooti 2 fat32-in-memory)))
      (list (code-char (bs_oemnamei 0 fat32-in-memory))
            (code-char (bs_oemnamei 1 fat32-in-memory))
            (code-char (bs_oemnamei 2 fat32-in-memory))
            (code-char (bs_oemnamei 3 fat32-in-memory))
            (code-char (bs_oemnamei 4 fat32-in-memory))
            (code-char (bs_oemnamei 5 fat32-in-memory))
            (code-char (bs_oemnamei 6 fat32-in-memory))
            (code-char (bs_oemnamei 7 fat32-in-memory)))
      (list (code-char (loghead 8 (bpb_bytspersec fat32-in-memory)))
            (code-char (logtail 8 (bpb_bytspersec fat32-in-memory)))
            (code-char (bpb_secperclus fat32-in-memory))
            (code-char (loghead 8 (bpb_rsvdseccnt fat32-in-memory)))
            (code-char (logtail 8 (bpb_rsvdseccnt fat32-in-memory))))
      ;; remaining reserved bytes
      (list (code-char (bpb_numfats fat32-in-memory))
            (code-char (loghead 8 (bpb_rootentcnt fat32-in-memory)))
            (code-char (logtail 8 (bpb_rootentcnt fat32-in-memory)))
            (code-char (loghead 8 (bpb_totsec16 fat32-in-memory)))
            (code-char (logtail 8 (bpb_totsec16 fat32-in-memory)))
            (code-char (bpb_media fat32-in-memory))
            (code-char (loghead 8 (bpb_fatsz16 fat32-in-memory)))
            (code-char (logtail 8 (bpb_fatsz16 fat32-in-memory)))
            (code-char (loghead 8 (bpb_secpertrk fat32-in-memory)))
            (code-char (logtail 8 (bpb_secpertrk fat32-in-memory)))
            (code-char (loghead 8 (bpb_numheads fat32-in-memory)))
            (code-char (logtail 8 (bpb_numheads fat32-in-memory)))
            (code-char (loghead 8             (bpb_hiddsec fat32-in-memory) ))
            (code-char (loghead 8 (logtail  8 (bpb_hiddsec fat32-in-memory))))
            (code-char (loghead 8 (logtail 16 (bpb_hiddsec fat32-in-memory))))
            (code-char            (logtail 24 (bpb_hiddsec fat32-in-memory)) )
            (code-char (loghead 8             (bpb_totsec32 fat32-in-memory) ))
            (code-char (loghead 8 (logtail  8 (bpb_totsec32 fat32-in-memory))))
            (code-char (loghead 8 (logtail 16 (bpb_totsec32 fat32-in-memory))))
            (code-char            (logtail 24 (bpb_totsec32 fat32-in-memory)) )
            (code-char (loghead 8             (bpb_fatsz32 fat32-in-memory) ))
            (code-char (loghead 8 (logtail  8 (bpb_fatsz32 fat32-in-memory))))
            (code-char (loghead 8 (logtail 16 (bpb_fatsz32 fat32-in-memory))))
            (code-char            (logtail 24 (bpb_fatsz32 fat32-in-memory)) )
            (code-char (loghead 8 (bpb_extflags fat32-in-memory)))
            (code-char (logtail 8 (bpb_extflags fat32-in-memory)))
            (code-char (bpb_fsver_minor fat32-in-memory))
            (code-char (bpb_fsver_major fat32-in-memory))
            (code-char (loghead 8             (bpb_rootclus fat32-in-memory) ))
            (code-char (loghead 8 (logtail  8 (bpb_rootclus fat32-in-memory))))
            (code-char (loghead 8 (logtail 16 (bpb_rootclus fat32-in-memory))))
            (code-char            (logtail 24 (bpb_rootclus fat32-in-memory)) )
            (code-char (loghead 8 (bpb_fsinfo fat32-in-memory)))
            (code-char (logtail 8 (bpb_fsinfo fat32-in-memory)))
            (code-char (loghead 8 (bpb_bkbootsec fat32-in-memory)))
            (code-char (logtail 8 (bpb_bkbootsec fat32-in-memory))))
      (list (code-char (bpb_reservedi  0 fat32-in-memory))
            (code-char (bpb_reservedi  1 fat32-in-memory))
            (code-char (bpb_reservedi  2 fat32-in-memory))
            (code-char (bpb_reservedi  3 fat32-in-memory))
            (code-char (bpb_reservedi  4 fat32-in-memory))
            (code-char (bpb_reservedi  5 fat32-in-memory))
            (code-char (bpb_reservedi  6 fat32-in-memory))
            (code-char (bpb_reservedi  7 fat32-in-memory))
            (code-char (bpb_reservedi  8 fat32-in-memory))
            (code-char (bpb_reservedi  9 fat32-in-memory))
            (code-char (bpb_reservedi 10 fat32-in-memory))
            (code-char (bpb_reservedi 11 fat32-in-memory)))
      (list (code-char (bs_drvnum fat32-in-memory))
            (code-char (bs_reserved1 fat32-in-memory))
            (code-char (bs_bootsig fat32-in-memory))
            (code-char (loghead 8             (bs_volid fat32-in-memory) ))
            (code-char (loghead 8 (logtail  8 (bs_volid fat32-in-memory))))
            (code-char (loghead 8 (logtail 16 (bs_volid fat32-in-memory))))
            (code-char            (logtail 24 (bs_volid fat32-in-memory)) ))
      (list (code-char (bs_vollabi  0 fat32-in-memory))
            (code-char (bs_vollabi  1 fat32-in-memory))
            (code-char (bs_vollabi  2 fat32-in-memory))
            (code-char (bs_vollabi  3 fat32-in-memory))
            (code-char (bs_vollabi  4 fat32-in-memory))
            (code-char (bs_vollabi  5 fat32-in-memory))
            (code-char (bs_vollabi  6 fat32-in-memory))
            (code-char (bs_vollabi  7 fat32-in-memory))
            (code-char (bs_vollabi  8 fat32-in-memory))
            (code-char (bs_vollabi  9 fat32-in-memory))
            (code-char (bs_vollabi 10 fat32-in-memory)))
      (list (code-char (bs_filsystypei 0 fat32-in-memory))
            (code-char (bs_filsystypei 1 fat32-in-memory))
            (code-char (bs_filsystypei 2 fat32-in-memory))
            (code-char (bs_filsystypei 3 fat32-in-memory))
            (code-char (bs_filsystypei 4 fat32-in-memory))
            (code-char (bs_filsystypei 5 fat32-in-memory))
            (code-char (bs_filsystypei 6 fat32-in-memory))
            (code-char (bs_filsystypei 7 fat32-in-memory)))
      (make-list
       (- (* (bpb_rsvdseccnt fat32-in-memory) (bpb_bytspersec fat32-in-memory)) 90)
       :initial-element (code-char 0)))
     'string)))

(defthm
  len-of-reserved-area-string
  (implies
   (and (integerp (* (bpb_bytspersec fat32-in-memory)
                     (bpb_rsvdseccnt fat32-in-memory)))
        (<= 90
            (* (bpb_bytspersec fat32-in-memory)
               (bpb_rsvdseccnt fat32-in-memory))))
   (equal (length (reserved-area-string fat32-in-memory))
          (* (bpb_rsvdseccnt fat32-in-memory)
             (bpb_bytspersec fat32-in-memory))))
  :hints (("goal" :in-theory (enable reserved-area-string))))

(defun
  make-fat-string-ac
  (n fat32-in-memory ac)
  (declare
   (xargs
    :stobjs fat32-in-memory
    :guard (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp n)
                (stringp ac))))
  (cond
   ((zp n) ac)
   (t
    (make-fat-string-ac
     (1- n)
     fat32-in-memory
     (concatenate
      'string
      (stobj-fa-table-to-string fat32-in-memory
                                (fat-length fat32-in-memory))
      ac)))))

(defund
  fat32-in-memory-to-string
  (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (compliant-fat32-in-memoryp fat32-in-memory)
          :verify-guards nil))
  (b*
      ((reserved-area-string
        (reserved-area-string fat32-in-memory))
       (fat-string
        (make-fat-string-ac
         (bpb_numfats fat32-in-memory) fat32-in-memory ""))
       (data-region-string
        ;; reproducing the definition of rchars-to-string because it doesn't
        ;; seem to be available to us
        (reverse (nats=>string
         (get-dir-ent-helper
          fat32-in-memory 0 (data-region-length fat32-in-memory) nil)))))
    (concatenate 'string
                 reserved-area-string
                 fat-string data-region-string)))

#|
Some (rather awful) testing forms are
(b* (((mv contents &)
      (get-clusterchain-contents fat32-in-memory 2 (ash 1 21))))
  (get-dir-filenames fat32-in-memory contents (ash 1 21)))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 (ash 1 21))))
  (fat32-in-memory-to-m1-fs fat32-in-memory dir-contents 40))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 (ash 1 21)))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory dir-contents 40)))
  (m1-open (list "INITRD  IMG")
           fs nil nil))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 (ash 1 21)))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory dir-contents 40))
     ((mv fd-table file-table & &)
      (m1-open (list "INITRD  IMG")
               fs nil nil)))
  (m1-pread 0 6 49 fs fd-table file-table))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 (ash 1 21)))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory dir-contents 40))
     ((mv fd-table file-table & &)
      (m1-open (list "INITRD  IMG")
               fs nil nil)))
  (m1-pwrite 0 "ornery" 49 fs fd-table file-table))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 (ash 1 21)))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory dir-contents 40))
     ((mv fd-table file-table & &)
      (m1-open (list "INITRD  IMG")
               fs nil nil))
     ((mv fs & &)
      (m1-pwrite 0 "ornery" 49 fs fd-table file-table))
     ((mv fat32-in-memory dir-ent-list)
      (m1-fs-to-fat32-in-memory-helper fat32-in-memory fs)))
  (mv fat32-in-memory dir-ent-list))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 (ash 1 21)))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory dir-contents 40))
     ((mv fd-table file-table & &)
      (m1-open (list "INITRD  IMG")
               fs nil nil))
     ((mv fs & &)
      (m1-pwrite 0 "ornery" 49 fs fd-table file-table)))
  (m1-fs-to-fat32-in-memory fat32-in-memory fs))
(time$
 (b*
     ((str (fat32-in-memory-to-string
            fat32-in-memory))
      ((unless (and (stringp str)
                    (>= (length str) *initialbytcnt*)))
       (mv fat32-in-memory -1))
      ((mv fat32-in-memory error-code)
       (read-reserved-area fat32-in-memory str))
      ((unless (equal error-code 0))
       (mv fat32-in-memory "it was read-reserved-area"))
      (fat-read-size (/ (* (bpb_fatsz32 fat32-in-memory)
                           (bpb_bytspersec fat32-in-memory))
                        4))
      ((unless (integerp fat-read-size))
       (mv fat32-in-memory "it was fat-read-size"))
      (data-byte-count (* (count-of-clusters fat32-in-memory)
                          (cluster-size fat32-in-memory)))
      ((unless (> data-byte-count 0))
       (mv fat32-in-memory "it was data-byte-count"))
      (tmp_bytspersec (bpb_bytspersec fat32-in-memory))
      (tmp_init (* tmp_bytspersec
                   (+ (bpb_rsvdseccnt fat32-in-memory)
                      (* (bpb_numfats fat32-in-memory)
                         (bpb_fatsz32 fat32-in-memory)))))
      ((unless (>= (length str)
                   (+ tmp_init
                      (data-region-length fat32-in-memory))))
       (mv fat32-in-memory "it was (length str)"))
      (fat32-in-memory (resize-fat fat-read-size fat32-in-memory))
      (fat32-in-memory
       (update-fat fat32-in-memory
                   (subseq str
                           (* (bpb_rsvdseccnt fat32-in-memory)
                              (bpb_bytspersec fat32-in-memory))
                           (+ (* (bpb_rsvdseccnt fat32-in-memory)
                                 (bpb_bytspersec fat32-in-memory))
                              (* fat-read-size 4)))
                   fat-read-size))
      (fat32-in-memory
       (resize-data-region data-byte-count fat32-in-memory))
      (data-region-string
       (subseq str tmp_init
               (+ tmp_init
                  (data-region-length fat32-in-memory))))
      (fat32-in-memory
       (update-data-region fat32-in-memory data-region-string
                           (data-region-length fat32-in-memory)
                           0)))
   (mv fat32-in-memory error-code)))
(time$
 (b*
     (((mv channel state)
       (open-output-channel "test/disk2.raw" :character state))
      (state
         (princ$
          (fat32-in-memory-to-string fat32-in-memory)
          channel state))
      (state
       (close-output-channel channel state)))
   (mv fat32-in-memory state)))
(b* (((mv dir-contents &)
      (get-clusterchain-contents fat32-in-memory 2 (ash 1 21)))
     (fs (fat32-in-memory-to-m1-fs fat32-in-memory dir-contents 40))
     ((mv fs & &)
      (m1-mkdir fs (list "" "TMP        "))))
  (m1-fs-to-fat32-in-memory fat32-in-memory fs))
|#

(defun
  get-dir-filenames
  (fat32-in-memory dir-contents entry-limit)
  (declare (xargs :measure (acl2-count entry-limit)
                  :verify-guards nil
                  :stobjs (fat32-in-memory)))
  (if
   (or (zp entry-limit)
       (equal (nth 0 dir-contents)
              0))
   nil
   (let*
    ((dir-ent (take 32 dir-contents))
     (first-cluster (combine32u (nth 21 dir-ent)
                                (nth 20 dir-ent)
                                (nth 27 dir-ent)
                                (nth 26 dir-ent)))
     (filename (nats=>string (subseq dir-ent 0 11))))
    (list*
     (if (or (zp (logand (nth 11 dir-ent)
                         (ash 1 4)))
             (equal filename ".          ")
             (equal filename "..         "))
         (list filename first-cluster)
       (b*
           (((mv contents &)
             (get-clusterchain
              fat32-in-memory
              (fat32-entry-mask first-cluster)
              (ash 1 21))) )
         (list filename first-cluster
               contents)))
     (get-dir-filenames
      fat32-in-memory (nthcdr 32 dir-contents)
      (- entry-limit 1))))))
