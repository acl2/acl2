(in-package "ACL2")

;  fat32-in-memory.lisp                                 Mihir Mehta

; These are the basic definitions and lemmas for a stobj model of the FAT32
; filesystem.

(include-book "../fat32")
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)

(make-event
 `(defstobj fat32$c

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
                 :initially ,*ms-min-count-of-clusters*)
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
    (fat :type (array (unsigned-byte 32) (*ms-min-count-of-clusters*))
         :resizable t
         ;; per spec
         :initially 0)

    (data-region :type (array string (*ms-min-count-of-clusters*))
         :resizable t
         ;; per spec
         :initially "")
    :renaming ((fat32$cp fat32$c-p))))

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
         (string-listp x))
  :rule-classes :definition)

(in-theory (disable bs_oemnamep bs_jmpbootp bs_filsystypep fatp data-regionp))

(in-theory (disable bpb_secperclus bpb_fatsz32 bpb_rsvdseccnt
                    bpb_numfats bpb_bytspersec bpb_rootclus bpb_fsinfo
                    bpb_bkbootsec bs_drvnum bs_reserved1 bs_bootsig
                    bpb_media bpb_fsver_minor bpb_fsver_major bpb_fatsz16
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
                    update-bpb_totsec16 update-bs_volid))

(in-theory (disable fati fat-length update-fati resize-fat
                    data-regioni data-region-length update-data-regioni
                    resize-data-region))

(defmacro
  update-stobj-scalar-correctness
    (bit-width updater accessor stobj stobj-recogniser constant lemma-name1
               lemma-name2 lemma-name3 lemma-name4 resize-data-region-of-updater
               updater-of-updater updater-of-accessor accessor-of-resize-fat
               fat-length-of-updater accessor-of-resize-data-region
               data-region-length-of-updater nth-of-updater)
  (let
      ((upper-bound (ash 1 bit-width)))
  `(encapsulate
     nil

     (defthm
       ,lemma-name1
       (implies (,stobj-recogniser ,stobj)
                (equal (,stobj-recogniser (,updater v ,stobj))
                       (unsigned-byte-p ,bit-width v)))
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
                                  (x (,accessor ,stobj))))))
        (:linear
         :corollary (implies (,stobj-recogniser ,stobj)
                             (and (<= 0 (,accessor ,stobj))
                                  (< (,accessor ,stobj) ,upper-bound))))))

     (defthm
       ,lemma-name3
       (equal (,accessor (,updater v ,stobj))
              v)
       :hints (("Goal" :in-theory (enable ,accessor ,updater))))

     (defthm
       ,lemma-name4
       (equal (resize-fat i (,updater v ,stobj))
              (,updater v (resize-fat i ,stobj)))
       :hints
       (("goal" :in-theory (enable resize-fat ,updater))))

     (defthm
       ,resize-data-region-of-updater
       (equal (resize-data-region i (,updater v ,stobj))
              (,updater v (resize-data-region i ,stobj)))
       :hints
       (("goal" :in-theory (enable resize-data-region ,updater))))

     (defthm
       ,updater-of-updater
       (equal (,updater
               v1
               (,updater v2 ,stobj))
              (,updater v1 ,stobj))
       :hints (("goal" :in-theory (enable ,updater))))

     (defthm
       ,updater-of-accessor
       (implies (,stobj-recogniser ,stobj)
                (equal (,updater
                        (,accessor ,stobj)
                        ,stobj)
                       ,stobj))
       :hints (("goal" :in-theory (enable ,updater ,accessor))))

     (defthm ,accessor-of-resize-fat
       (equal (,accessor (resize-fat i ,stobj))
              (,accessor ,stobj))
       :hints (("goal" :in-theory (enable resize-fat ,accessor))))

     (defthm ,fat-length-of-updater
       (equal (fat-length (,updater v ,stobj))
              (fat-length ,stobj))
       :hints (("goal" :in-theory (enable fat-length ,updater))))

     (defthm ,accessor-of-resize-data-region
       (equal (,accessor (resize-data-region i ,stobj))
              (,accessor ,stobj))
       :hints (("goal" :in-theory (enable resize-data-region ,accessor))))

     (defthm ,data-region-length-of-updater
       (equal (data-region-length (,updater v ,stobj))
              (data-region-length ,stobj))
       :hints (("goal" :in-theory (enable data-region-length ,updater))))

     (defthm ,nth-of-updater
       (equal (nth n (,updater v ,stobj))
              (if (equal n ,constant)
                  v
                (nth n ,stobj)))
       :hints (("goal" :in-theory (enable data-region-length ,updater)))))))

(update-stobj-scalar-correctness 16 update-bpb_rsvdseccnt bpb_rsvdseccnt
                                 fat32$c fat32$c-p
                                 *bpb_rsvdseccnt*
                                 update-bpb_rsvdseccnt-correctness-1
                                 update-bpb_rsvdseccnt-correctness-2
                                 update-bpb_rsvdseccnt-correctness-3
                                 update-bpb_rsvdseccnt-correctness-4
                                 update-bpb_rsvdseccnt-correctness-5
                                 update-bpb_rsvdseccnt-of-update-bpb_rsvdseccnt
                                 update-bpb_rsvdseccnt-of-bpb_rsvdseccnt
                                 bpb_rsvdseccnt-of-resize-fat
                                 fat-length-of-bpb_rsvdseccnt
                                 bpb_rsvdseccnt-of-resize-data-region
                                 data-region-length-of-bpb_rsvdseccnt
                                 nth-of-bpb_rsvdseccnt)

(update-stobj-scalar-correctness 8 update-bpb_secperclus bpb_secperclus
                                 fat32$c fat32$c-p
                                 *bpb_secperclus*
                                 update-bpb_secperclus-correctness-1
                                 update-bpb_secperclus-correctness-2
                                 update-bpb_secperclus-correctness-3
                                 update-bpb_secperclus-correctness-4
                                 update-bpb_secperclus-correctness-5
                                 update-bpb_secperclus-of-update-bpb_secperclus
                                 update-bpb_secperclus-of-bpb_secperclus
                                 bpb_secperclus-of-resize-fat
                                 fat-length-of-bpb_secperclus
                                 bpb_secperclus-of-resize-data-region
                                 data-region-length-of-bpb_secperclus
                                 nth-of-bpb_secperclus)

(update-stobj-scalar-correctness 16 update-bpb_bytspersec bpb_bytspersec
                                 fat32$c fat32$c-p
                                 *bpb_bytspersec*
                                 update-bpb_bytspersec-correctness-1
                                 update-bpb_bytspersec-correctness-2
                                 update-bpb_bytspersec-correctness-3
                                 update-bpb_bytspersec-correctness-4
                                 update-bpb_bytspersec-correctness-5
                                 update-bpb_bytspersec-of-update-bpb_bytspersec
                                 update-bpb_bytspersec-of-bpb_bytspersec
                                 bpb_bytspersec-of-resize-fat
                                 fat-length-of-bpb_bytspersec
                                 bpb_bytspersec-of-resize-data-region
                                 data-region-length-of-bpb_bytspersec
                                 nth-of-bpb_bytspersec)

(update-stobj-scalar-correctness 8 update-bpb_numfats bpb_numfats
                                 fat32$c fat32$c-p
                                 *bpb_numfats*
                                 update-bpb_numfats-correctness-1
                                 update-bpb_numfats-correctness-2
                                 update-bpb_numfats-correctness-3
                                 update-bpb_numfats-correctness-4
                                 update-bpb_numfats-correctness-5
                                 update-bpb_numfats-of-update-bpb_numfats
                                 update-bpb_numfats-of-bpb_numfats
                                 bpb_numfats-of-resize-fat
                                 fat-length-of-bpb_numfats
                                 bpb_numfats-of-resize-data-region
                                 data-region-length-of-bpb_numfats
                                 nth-of-bpb_numfats)

(update-stobj-scalar-correctness 32 update-bpb_rootclus bpb_rootclus
                                 fat32$c fat32$c-p
                                 *bpb_rootclus*
                                 update-bpb_rootclus-correctness-1
                                 update-bpb_rootclus-correctness-2
                                 update-bpb_rootclus-correctness-3
                                 update-bpb_rootclus-correctness-4
                                 update-bpb_rootclus-correctness-5
                                 update-bpb_rootclus-of-update-bpb_rootclus
                                 update-bpb_rootclus-of-bpb_rootclus
                                 bpb_rootclus-of-resize-fat
                                 fat-length-of-bpb_rootclus
                                 bpb_rootclus-of-resize-data-region
                                 data-region-length-of-bpb_rootclus
                                 nth-of-bpb_rootclus)

(update-stobj-scalar-correctness 16 update-bpb_fsinfo bpb_fsinfo
                                 fat32$c fat32$c-p
                                 *bpb_fsinfo*
                                 update-bpb_fsinfo-correctness-1
                                 update-bpb_fsinfo-correctness-2
                                 update-bpb_fsinfo-correctness-3
                                 update-bpb_fsinfo-correctness-4
                                 update-bpb_fsinfo-correctness-5
                                 update-bpb_fsinfo-of-update-bpb_fsinfo
                                 update-bpb_fsinfo-of-bpb_fsinfo
                                 bpb_fsinfo-of-resize-fat
                                 fat-length-of-bpb_fsinfo
                                 bpb_fsinfo-of-resize-data-region
                                 data-region-length-of-bpb_fsinfo
                                 nth-of-bpb_fsinfo)

(update-stobj-scalar-correctness 16 update-bpb_bkbootsec bpb_bkbootsec
                                 fat32$c fat32$c-p
                                 *bpb_bkbootsec*
                                 update-bpb_bkbootsec-correctness-1
                                 update-bpb_bkbootsec-correctness-2
                                 update-bpb_bkbootsec-correctness-3
                                 update-bpb_bkbootsec-correctness-4
                                 update-bpb_bkbootsec-correctness-5
                                 update-bpb_bkbootsec-of-update-bpb_bkbootsec
                                 update-bpb_bkbootsec-of-bpb_bkbootsec
                                 bpb_bkbootsec-of-resize-fat
                                 fat-length-of-bpb_bkbootsec
                                 bpb_bkbootsec-of-resize-data-region
                                 data-region-length-of-bpb_bkbootsec
                                 nth-of-bpb_bkbootsec)

(update-stobj-scalar-correctness 8 update-bs_drvnum bs_drvnum
                                 fat32$c fat32$c-p
                                 *bs_drvnum*
                                 update-bs_drvnum-correctness-1
                                 update-bs_drvnum-correctness-2
                                 update-bs_drvnum-correctness-3
                                 update-bs_drvnum-correctness-4
                                 update-bs_drvnum-correctness-5
                                 update-bs_drvnum-of-update-bs_drvnum
                                 update-bs_drvnum-of-bs_drvnum
                                 bs_drvnum-of-resize-fat
                                 fat-length-of-bs_drvnum
                                 bs_drvnum-of-resize-data-region
                                 data-region-length-of-bs_drvnum
                                 nth-of-bs_drvnum)

(update-stobj-scalar-correctness 8 update-bs_reserved1 bs_reserved1
                                 fat32$c fat32$c-p
                                 *bs_reserved1*
                                 update-bs_reserved1-correctness-1
                                 update-bs_reserved1-correctness-2
                                 update-bs_reserved1-correctness-3
                                 update-bs_reserved1-correctness-4
                                 update-bs_reserved1-correctness-5
                                 update-bs_reserved1-of-update-bs_reserved1
                                 update-bs_reserved1-of-bs_reserved1
                                 bs_reserved1-of-resize-fat
                                 fat-length-of-bs_reserved1
                                 bs_reserved1-of-resize-data-region
                                 data-region-length-of-bs_reserved1
                                 nth-of-bs_reserved1)

(update-stobj-scalar-correctness 8 update-bs_bootsig bs_bootsig
                                 fat32$c fat32$c-p
                                 *bs_bootsig*
                                 update-bs_bootsig-correctness-1
                                 update-bs_bootsig-correctness-2
                                 update-bs_bootsig-correctness-3
                                 update-bs_bootsig-correctness-4
                                 update-bs_bootsig-correctness-5
                                 update-bs_bootsig-of-update-bs_bootsig
                                 update-bs_bootsig-of-bs_bootsig
                                 bs_bootsig-of-resize-fat
                                 fat-length-of-bs_bootsig
                                 bs_bootsig-of-resize-data-region
                                 data-region-length-of-bs_bootsig
                                 nth-of-bs_bootsig)

(update-stobj-scalar-correctness 8 update-bpb_media bpb_media
                                 fat32$c fat32$c-p
                                 *bpb_media*
                                 update-bpb_media-correctness-1
                                 update-bpb_media-correctness-2
                                 update-bpb_media-correctness-3
                                 update-bpb_media-correctness-4
                                 update-bpb_media-correctness-5
                                 update-bpb_media-of-update-bpb_media
                                 update-bpb_media-of-bpb_media
                                 bpb_media-of-resize-fat
                                 fat-length-of-bpb_media
                                 bpb_media-of-resize-data-region
                                 data-region-length-of-bpb_media
                                 nth-of-bpb_media)

(update-stobj-scalar-correctness 8 update-bpb_fsver_minor bpb_fsver_minor
                                 fat32$c fat32$c-p
                                 *bpb_fsver_minor*
                                 update-bpb_fsver_minor-correctness-1
                                 update-bpb_fsver_minor-correctness-2
                                 update-bpb_fsver_minor-correctness-3
                                 update-bpb_fsver_minor-correctness-4
                                 update-bpb_fsver_minor-correctness-5
                                 update-bpb_fsver_minor-of-update-bpb_fsver_minor
                                 update-bpb_fsver_minor-of-bpb_fsver_minor
                                 bpb_fsver_minor-of-resize-fat
                                 fat-length-of-bpb_fsver_minor
                                 bpb_fsver_minor-of-resize-data-region
                                 data-region-length-of-bpb_fsver_minor
                                 nth-of-bpb_fsver_minor)

(update-stobj-scalar-correctness 8 update-bpb_fsver_major bpb_fsver_major
                                 fat32$c fat32$c-p
                                 *bpb_fsver_major*
                                 update-bpb_fsver_major-correctness-1
                                 update-bpb_fsver_major-correctness-2
                                 update-bpb_fsver_major-correctness-3
                                 update-bpb_fsver_major-correctness-4
                                 update-bpb_fsver_major-correctness-5
                                 update-bpb_fsver_major-of-update-bpb_fsver_major
                                 update-bpb_fsver_major-of-bpb_fsver_major
                                 bpb_fsver_major-of-resize-fat
                                 fat-length-of-bpb_fsver_major
                                 bpb_fsver_major-of-resize-data-region
                                 data-region-length-of-bpb_fsver_major
                                 nth-of-bpb_fsver_major)

(update-stobj-scalar-correctness 16 update-bpb_fatsz16 bpb_fatsz16
                                 fat32$c fat32$c-p
                                 *bpb_fatsz16*
                                 update-bpb_fatsz16-correctness-1
                                 update-bpb_fatsz16-correctness-2
                                 update-bpb_fatsz16-correctness-3
                                 update-bpb_fatsz16-correctness-4
                                 update-bpb_fatsz16-correctness-5
                                 update-bpb_fatsz16-of-update-bpb_fatsz16
                                 update-bpb_fatsz16-of-bpb_fatsz16
                                 bpb_fatsz16-of-resize-fat
                                 fat-length-of-bpb_fatsz16
                                 bpb_fatsz16-of-resize-data-region
                                 data-region-length-of-bpb_fatsz16
                                 nth-of-bpb_fatsz16)

(update-stobj-scalar-correctness 16 update-bpb_secpertrk bpb_secpertrk
                                 fat32$c fat32$c-p
                                 *bpb_secpertrk*
                                 update-bpb_secpertrk-correctness-1
                                 update-bpb_secpertrk-correctness-2
                                 update-bpb_secpertrk-correctness-3
                                 update-bpb_secpertrk-correctness-4
                                 update-bpb_secpertrk-correctness-5
                                 update-bpb_secpertrk-of-update-bpb_secpertrk
                                 update-bpb_secpertrk-of-bpb_secpertrk
                                 bpb_secpertrk-of-resize-fat
                                 fat-length-of-bpb_secpertrk
                                 bpb_secpertrk-of-resize-data-region
                                 data-region-length-of-bpb_secpertrk
                                 nth-of-bpb_secpertrk)

(update-stobj-scalar-correctness 16 update-bpb_numheads bpb_numheads
                                 fat32$c fat32$c-p
                                 *bpb_numheads*
                                 update-bpb_numheads-correctness-1
                                 update-bpb_numheads-correctness-2
                                 update-bpb_numheads-correctness-3
                                 update-bpb_numheads-correctness-4
                                 update-bpb_numheads-correctness-5
                                 update-bpb_numheads-of-update-bpb_numheads
                                 update-bpb_numheads-of-bpb_numheads
                                 bpb_numheads-of-resize-fat
                                 fat-length-of-bpb_numheads
                                 bpb_numheads-of-resize-data-region
                                 data-region-length-of-bpb_numheads
                                 nth-of-bpb_numheads)

(update-stobj-scalar-correctness 16 update-bpb_extflags bpb_extflags
                                 fat32$c fat32$c-p
                                 *bpb_extflags*
                                 update-bpb_extflags-correctness-1
                                 update-bpb_extflags-correctness-2
                                 update-bpb_extflags-correctness-3
                                 update-bpb_extflags-correctness-4
                                 update-bpb_extflags-correctness-5
                                 update-bpb_extflags-of-update-bpb_extflags
                                 update-bpb_extflags-of-bpb_extflags
                                 bpb_extflags-of-resize-fat
                                 fat-length-of-bpb_extflags
                                 bpb_extflags-of-resize-data-region
                                 data-region-length-of-bpb_extflags
                                 nth-of-bpb_extflags)

(update-stobj-scalar-correctness 32 update-bpb_hiddsec bpb_hiddsec
                                 fat32$c fat32$c-p
                                 *bpb_hiddsec*
                                 update-bpb_hiddsec-correctness-1
                                 update-bpb_hiddsec-correctness-2
                                 update-bpb_hiddsec-correctness-3
                                 update-bpb_hiddsec-correctness-4
                                 update-bpb_hiddsec-correctness-5
                                 update-bpb_hiddsec-of-update-bpb_hiddsec
                                 update-bpb_hiddsec-of-bpb_hiddsec
                                 bpb_hiddsec-of-resize-fat
                                 fat-length-of-bpb_hiddsec
                                 bpb_hiddsec-of-resize-data-region
                                 data-region-length-of-bpb_hiddsec
                                 nth-of-bpb_hiddsec)

(update-stobj-scalar-correctness 32 update-bpb_totsec32 bpb_totsec32
                                 fat32$c fat32$c-p
                                 *bpb_totsec32*
                                 update-bpb_totsec32-correctness-1
                                 update-bpb_totsec32-correctness-2
                                 update-bpb_totsec32-correctness-3
                                 update-bpb_totsec32-correctness-4
                                 update-bpb_totsec32-correctness-5
                                 update-bpb_totsec32-of-update-bpb_totsec32
                                 update-bpb_totsec32-of-bpb_totsec32
                                 bpb_totsec32-of-resize-fat
                                 fat-length-of-bpb_totsec32
                                 bpb_totsec32-of-resize-data-region
                                 data-region-length-of-bpb_totsec32
                                 nth-of-bpb_totsec32)

(update-stobj-scalar-correctness 32 update-bpb_fatsz32 bpb_fatsz32
                                 fat32$c fat32$c-p
                                 *bpb_fatsz32*
                                 update-bpb_fatsz32-correctness-1
                                 update-bpb_fatsz32-correctness-2
                                 update-bpb_fatsz32-correctness-3
                                 update-bpb_fatsz32-correctness-4
                                 update-bpb_fatsz32-correctness-5
                                 update-bpb_fatsz32-of-update-bpb_fatsz32
                                 update-bpb_fatsz32-of-bpb_fatsz32
                                 bpb_fatsz32-of-resize-fat
                                 fat-length-of-bpb_fatsz32
                                 bpb_fatsz32-of-resize-data-region
                                 data-region-length-of-bpb_fatsz32
                                 nth-of-bpb_fatsz32)

(update-stobj-scalar-correctness 16 update-bpb_rootentcnt bpb_rootentcnt
                                 fat32$c fat32$c-p
                                 *bpb_rootentcnt*
                                 update-bpb_rootentcnt-correctness-1
                                 update-bpb_rootentcnt-correctness-2
                                 update-bpb_rootentcnt-correctness-3
                                 update-bpb_rootentcnt-correctness-4
                                 update-bpb_rootentcnt-correctness-5
                                 update-bpb_rootentcnt-of-update-bpb_rootentcnt
                                 update-bpb_rootentcnt-of-bpb_rootentcnt
                                 bpb_rootentcnt-of-resize-fat
                                 fat-length-of-bpb_rootentcnt
                                 bpb_rootentcnt-of-resize-data-region
                                 data-region-length-of-bpb_rootentcnt
                                 nth-of-bpb_rootentcnt)

(update-stobj-scalar-correctness 16 update-bpb_totsec16 bpb_totsec16
                                 fat32$c fat32$c-p
                                 *bpb_totsec16*
                                 update-bpb_totsec16-correctness-1
                                 update-bpb_totsec16-correctness-2
                                 update-bpb_totsec16-correctness-3
                                 update-bpb_totsec16-correctness-4
                                 update-bpb_totsec16-correctness-5
                                 update-bpb_totsec16-of-update-bpb_totsec16
                                 update-bpb_totsec16-of-bpb_totsec16
                                 bpb_totsec16-of-resize-fat
                                 fat-length-of-bpb_totsec16
                                 bpb_totsec16-of-resize-data-region
                                 data-region-length-of-bpb_totsec16
                                 nth-of-bpb_totsec16)

(update-stobj-scalar-correctness 32 update-bs_volid bs_volid
                                 fat32$c fat32$c-p
                                 *bs_volid*
                                 update-bs_volid-correctness-1
                                 update-bs_volid-correctness-2
                                 update-bs_volid-correctness-3
                                 update-bs_volid-correctness-4
                                 update-bs_volid-correctness-5
                                 update-bs_volid-of-update-bs_volid
                                 update-bs_volid-of-bs_volid
                                 bs_volid-of-resize-fat
                                 fat-length-of-bs_volid
                                 bs_volid-of-resize-data-region
                                 data-region-length-of-bs_volid
                                 nth-of-bs_volid)

(defthm fati-of-update-fati
  (equal (fati i1 (update-fati i2 v fat32$c))
         (if (equal (nfix i1) (nfix i2))
             v (fati i1 fat32$c)))
  :hints (("goal" :in-theory (enable fati update-fati))))

(defthm
  data-regioni-of-update-data-regioni
  (equal
   (data-regioni i1
                 (update-data-regioni i2 v fat32$c))
   (if (equal (nfix i1) (nfix i2))
       v (data-regioni i1 fat32$c)))
  :hints
  (("goal"
    :in-theory (enable data-regioni update-data-regioni))))

(defthm
  data-region-length-of-resize-fat
  (equal (data-region-length (resize-fat i fat32$c))
         (data-region-length fat32$c))
  :hints
  (("goal" :in-theory (enable data-region-length resize-fat))))

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
        (bpb_fatsz32 (update-nth key val fat32$c))
        (bpb_fatsz32 fat32$c)))
      :hints (("goal" :in-theory (enable bpb_fatsz32)))
      :rule-classes
      ,(make-corollaries
        'bpb_fatsz32
        (remove1-assoc 'update-bpb_fatsz32 *the-list*)
        'fat32$c)))

  (make-event
   `(defthm
      bpb_secperclus-of-update-nth
      (implies
       (not (equal key *bpb_secperclus*))
       (equal (bpb_secperclus (update-nth key val fat32$c))
              (bpb_secperclus fat32$c)))
      :hints (("goal" :in-theory (enable bpb_secperclus)))
      :rule-classes
      ,(make-corollaries
        'bpb_secperclus
        (remove1-assoc 'update-bpb_secperclus *the-list*)
        'fat32$c)))

  (make-event
   `(defthm
      bpb_rsvdseccnt-of-update-nth
      (implies
       (not (equal key *bpb_rsvdseccnt*))
       (equal
        (bpb_rsvdseccnt (update-nth key val fat32$c))
        (bpb_rsvdseccnt fat32$c)))
      :hints (("goal" :in-theory (enable bpb_rsvdseccnt)))
      :rule-classes
      ,(make-corollaries
        'bpb_rsvdseccnt
        (remove1-assoc 'update-bpb_rsvdseccnt *the-list*)
        'fat32$c)))

  (make-event
   `(defthm
      bpb_numfats-of-update-nth
      (implies
       (not (equal key *bpb_numfats*))
       (equal
        (bpb_numfats (update-nth key val fat32$c))
        (bpb_numfats fat32$c)))
      :hints (("goal" :in-theory (enable bpb_numfats)))
      :rule-classes
      ,(make-corollaries
        'bpb_numfats
        (remove1-assoc 'update-bpb_numfats *the-list*)
        'fat32$c)))

  (make-event
   `(defthm
      bpb_bytspersec-of-update-nth
      (implies
       (not (equal key *bpb_bytspersec*))
       (equal
        (bpb_bytspersec (update-nth key val fat32$c))
        (bpb_bytspersec fat32$c)))
      :hints (("goal" :in-theory (enable bpb_bytspersec)))
      :rule-classes
      ,(make-corollaries
        'bpb_bytspersec
        (remove1-assoc 'update-bpb_bytspersec *the-list*)
        'fat32$c)))

  (make-event
   `(defthm
      bpb_totsec32-of-update-nth
      (implies
       (not (equal key *bpb_totsec32*))
       (equal
        (bpb_totsec32 (update-nth key val fat32$c))
        (bpb_totsec32 fat32$c)))
      :hints (("goal" :in-theory (enable bpb_totsec32)))
      :rule-classes
      ,(make-corollaries
        'bpb_totsec32
        (remove1-assoc 'update-bpb_totsec32 *the-list*)
        'fat32$c)))

  (make-event
   `(defthm
      bpb_rootclus-of-update-nth
      (implies
       (not (equal key *bpb_rootclus*))
       (equal
        (bpb_rootclus (update-nth key val fat32$c))
        (bpb_rootclus fat32$c)))
      :hints (("goal" :in-theory (enable bpb_rootclus)))
      :rule-classes
      ,(make-corollaries
        'bpb_rootclus
        (remove1-assoc 'update-bpb_rootclus *the-list*)
        'fat32$c))))

(defthm bpb_rootclus-of-update-fati
  (equal (bpb_rootclus (update-fati i v fat32$c))
         (bpb_rootclus fat32$c))
  :hints (("Goal" :in-theory (enable update-fati))))

(defthm bpb_rootclus-of-update-data-regioni
  (equal (bpb_rootclus (update-data-regioni i v fat32$c))
         (bpb_rootclus fat32$c))
  :hints (("Goal" :in-theory (enable update-data-regioni))))

(defthm
  fat-length-of-update-fati
  (equal (fat-length (update-fati i v fat32$c))
         (max (fat-length fat32$c)
              (1+ (nfix i))))
  :hints (("goal" :in-theory (enable fat-length update-fati))))

(defthm
  fat-length-of-resize-fat
  (equal (fat-length (resize-fat i fat32$c))
         (nfix i))
  :hints (("goal" :in-theory (enable fat-length resize-fat))))

(defthm
  data-regioni-of-update-fati
  (equal (data-regioni i1 (update-fati i2 v fat32$c))
         (data-regioni i1 fat32$c))
  :hints
  (("goal"
    :in-theory (enable data-regioni update-fati))))

(defthm
  data-region-length-of-update-data-regioni
  (equal (data-region-length (update-data-regioni i v fat32$c))
         (max (data-region-length fat32$c)
              (1+ (nfix i))))
  :hints (("goal" :in-theory (enable data-region-length update-data-regioni)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (equal (consp (nth *data-regioni* (update-data-regioni i v fat32$c)))
           (not (zp (max (data-region-length fat32$c)
                         (1+ (nfix i))))))
    :hints (("Goal"
             :in-theory (enable data-region-length)) ))))

(defthm
  fati-of-update-data-regioni
  (equal (fati i1
               (update-data-regioni i2 v fat32$c))
         (fati i1 fat32$c))
  :hints
  (("goal" :in-theory (enable fati update-data-regioni))))

(defthm
  data-region-length-of-resize-data-region
  (equal (data-region-length
          (resize-data-region i data-region32-in-memory))
         (nfix i))
  :hints (("goal" :in-theory (enable data-region-length
                                     resize-data-region))))

(defmacro
  update-stobj-array
  (name array-length bit-width array-updater array-accessor constant
        stobj stobj-recogniser lemma-name1 lemma-name2 lemma-name3
        unsigned-byte-p-of-array-accessor lemma-name5 lemma-name6 lemma-name7
        lemma-name8 lemma-name9 name-alt nth-of-name-1 nth-of-name-2)
  (let
      ((upper-bound (ash 1 bit-width)))
  `(encapsulate
     nil

     (defun
       ,name (v ,stobj)
       (declare
        (xargs
         :guard (and (unsigned-byte-listp ,bit-width v)
                     (<= (len v)
                         (,array-length ,stobj))
                     (,stobj-recogniser ,stobj))
         :guard-hints
         (("goal" :in-theory (disable ,stobj-recogniser unsigned-byte-p)))
         :stobjs (,stobj)))
       (if
           (atom v)
           ,stobj
        (let* ((,stobj
                (,array-updater (- (,array-length ,stobj)
                                       (len v))
                                (car v)
                                ,stobj))
               (,stobj (,name (cdr v)
                              ,stobj)))
          ,stobj)))

     (defthm
       ,lemma-name1
       t
       :rule-classes
       ((:rewrite :corollary
                   (equal (bpb_secperclus (,name v ,stobj))
                          (bpb_secperclus fat32$c))
                   :hints (("Goal" :in-theory (enable bpb_secperclus)) ))
        (:rewrite :corollary
                   (equal (bpb_rsvdseccnt (,name v ,stobj))
                          (bpb_rsvdseccnt fat32$c))
                  :hints (("Goal" :in-theory (enable bpb_rsvdseccnt)) ))
        (:rewrite :corollary
                   (equal (bpb_numfats (,name v ,stobj))
                          (bpb_numfats fat32$c))
                  :hints (("Goal" :in-theory (enable bpb_numfats)) ))
        (:rewrite :corollary
                   (equal (bpb_fatsz32 (,name v ,stobj))
                          (bpb_fatsz32 fat32$c))
                  :hints (("Goal" :in-theory (enable bpb_fatsz32)) ))
        (:rewrite :corollary
                   (equal (bpb_bytspersec (,name v ,stobj))
                          (bpb_bytspersec fat32$c))
                   :hints (("Goal" :in-theory (enable bpb_bytspersec)) ))
        (:rewrite :corollary
                   (equal (bpb_totsec32 (,name v ,stobj))
                          (bpb_totsec32 fat32$c))
                   :hints (("Goal" :in-theory (enable bpb_totsec32)) ))
        (:rewrite :corollary
                   (equal (bpb_rootclus (,name v ,stobj))
                          (bpb_rootclus fat32$c))
                   :hints (("Goal" :in-theory (enable bpb_rootclus)) ))))

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
          (equal (len (nth ,constant
                           (,array-updater i v ,stobj)))
                 (len (nth ,constant ,stobj)))))))

     (defthm ,lemma-name3
       (implies (and (unsigned-byte-listp ,bit-width v)
                     (<= (len v)
                         (,array-length ,stobj))
                     (,stobj-recogniser ,stobj))
                (,stobj-recogniser (,name v ,stobj)))
       :hints (("goal" :in-theory (e/d (unsigned-byte-listp)
                                       (,stobj-recogniser ,array-updater))
                :induct
                (,stobj-recogniser (,name v ,stobj)))))

     (defthm ,unsigned-byte-p-of-array-accessor
       (implies (,stobj-recogniser ,stobj)
                (equal
                 (unsigned-byte-p ,bit-width (,array-accessor i ,stobj))
                 (< (nfix i) (,array-length ,stobj))))
       :hints (("Goal" :in-theory (disable unsigned-byte-p)))
       :rule-classes
       (:rewrite
        (:rewrite
         :corollary
         (implies (and
                   (,stobj-recogniser ,stobj)
                   (< (nfix i) (,array-length ,stobj)))
                  (integerp (,array-accessor i ,stobj)))
         :hints (("Goal" :in-theory (disable fat32$c-p))))
        (:linear
         :corollary
         (implies (and
                   (,stobj-recogniser ,stobj)
                   (< (nfix i) (,array-length ,stobj)))
                  (and
                   (<= 0 (,array-accessor i ,stobj))
                   (< (,array-accessor i ,stobj) ,upper-bound)))
         :hints (("Goal" :in-theory (disable fat32$c-p))))))

     (defthm ,lemma-name5
       (equal
        (resize-fat i
                    (,name v ,stobj))
        (,name v (resize-fat i ,stobj)))
       :hints (("goal" :in-theory (enable resize-fat))))

     (defthm ,lemma-name6
       (equal
        (resize-data-region i
                    (,name v ,stobj))
        (,name v (resize-data-region i ,stobj)))
       :hints (("goal" :in-theory (enable resize-data-region))))

     (defthm ,lemma-name7
       (equal (fat-length (,name v ,stobj))
              (fat-length ,stobj))
       :hints (("goal" :in-theory (enable fat-length))))

     (defthm ,lemma-name8
       (equal (data-region-length (,name v ,stobj))
              (data-region-length ,stobj))
       :hints (("goal" :in-theory (enable data-region-length))))

     ;; Why didn't this work with nfix?
     (defthm ,lemma-name9
       (implies
        (and (,stobj-recogniser ,stobj)
             (natp i)
             (< i (,array-length ,stobj)))
        (equal (,array-updater i (,array-accessor i ,stobj) ,stobj)
               ,stobj)))

     (defthmd ,name-alt
       (implies
        (and (<= (len v)
                 (,array-length ,stobj))
             (,stobj-recogniser ,stobj)
             (unsigned-byte-listp ,bit-width v))
        (equal
         (,name v ,stobj)
         (update-nth
          ,constant
          (append (take (- (,array-length ,stobj)
                           (len v))
                        (nth ,constant ,stobj))
                  (true-list-fix v))
          ,stobj)))
       :hints
       (("goal" :in-theory (enable ,array-length
                                   remember-that-time-with-update-nth))))

     (defthm ,nth-of-name-1
       (implies
        (not (equal (nfix n) ,constant))
        (equal (nth n (,name v ,stobj))
               (nth n ,stobj))))

     (defthm ,nth-of-name-2
       (implies
        (and (<= (len v)
                 (,array-length ,stobj))
             (,stobj-recogniser ,stobj)
             (unsigned-byte-listp ,bit-width v))
        (equal
         (nth ,constant (,name v ,stobj))
         (append (take (- (,array-length ,stobj)
                          (len v))
                       (nth ,constant ,stobj))
                 (true-list-fix v))))
       :hints
       (("goal" :use ,name-alt))))))

(update-stobj-array
 update-bs_jmpboot bs_jmpboot-length 8
 update-bs_jmpbooti bs_jmpbooti *bs_jmpbooti*
 fat32$c fat32$c-p
 update-bs_jmpboot-correctness-1
 update-bs_jmpboot-correctness-2
 update-bs_jmpboot-correctness-3
 unsigned-byte-p-of-update-bs_jmpbooti
 update-bs_jmpboot-correctness-5
 update-bs_jmpboot-correctness-6
 update-bs_jmpboot-correctness-7
 data-region-length-of-update-bs_jmpboot
 update-bs_jmpbooti-of-bs_jmpbooti
 update-bs_jmpboot-alt
 nth-of-bs_jmpboot-1
 nth-of-bs_jmpboot-2)

(update-stobj-array
 update-bs_oemname bs_oemname-length 8
 update-bs_oemnamei bs_oemnamei *bs_oemnamei*
 fat32$c fat32$c-p
 update-bs_oemname-correctness-1
 update-bs_oemname-correctness-2
 update-bs_oemname-correctness-3
 unsigned-byte-p-of-update-bs_oemnamei
 update-bs_oemname-correctness-5
 update-bs_oemname-correctness-6
 update-bs_oemname-correctness-7
 data-region-length-of-update-bs_oemname
 update-bs_oemnamei-of-bs_oemnamei
 update-bs_oemname-alt
 nth-of-bs_oemname-1
 nth-of-bs_oemname-2)

(update-stobj-array
 update-bs_vollab bs_vollab-length 8
 update-bs_vollabi bs_vollabi *bs_vollabi*
 fat32$c fat32$c-p
 update-bs_vollab-correctness-1
 update-bs_vollab-correctness-2
 update-bs_vollab-correctness-3
 unsigned-byte-p-of-update-bs_vollabi
 update-bs_vollab-correctness-5
 update-bs_vollab-correctness-6
 update-bs_vollab-correctness-7
 data-region-length-of-update-bs_vollab
 update-bs_vollabi-of-bs_vollabi
 update-bs_vollab-alt
 nth-of-bs_vollab-1
 nth-of-bs_vollab-2)

(update-stobj-array
 update-bs_filsystype bs_filsystype-length 8
 update-bs_filsystypei bs_filsystypei *bs_filsystypei*
 fat32$c fat32$c-p
 update-bs_filsystype-correctness-1
 update-bs_filsystype-correctness-2
 update-bs_filsystype-correctness-3
 unsigned-byte-p-of-update-bs_filsystypei
 update-bs_filsystype-correctness-5
 update-bs_filsystype-correctness-6
 update-bs_filsystype-correctness-7
 data-region-length-of-update-bs_filsystype
 update-bs_filsystypei-of-bs_filsystypei
 update-bs_filsystype-alt
 nth-of-bs_filsystype-1
 nth-of-bs_filsystype-2)

(update-stobj-array
 update-bpb_reserved bpb_reserved-length 8
 update-bpb_reservedi bpb_reservedi *bpb_reservedi*
 fat32$c fat32$c-p
 update-bpb_reserved-correctness-1
 update-bpb_reserved-correctness-2
 update-bpb_reserved-correctness-3
 unsigned-byte-p-of-update-bpb_reservedi
 update-bpb_reserved-correctness-5
 update-bpb_reserved-correctness-6
 update-bpb_reserved-correctness-7
 data-region-length-of-update-bpb_reserved
 update-bpb_reservedi-of-bpb_reservedi
 update-bpb_reserved-alt
 nth-of-bpb_reserved-1
 nth-of-bpb_reserved-2)

(comp t) ; Matt K. mod 4/2019 (needed for avoiding stack overflow in Allegro CL)

(defthm
  fat32$c-p-of-create-fat32$c
  (fat32$c-p (create-fat32$c)))

;; The strategy of just using lofat-fs-p everywhere is not
;; going to work. It's going to be desirable to prove lemmas with the weaker
;; hypothesis (fat32$c-p fat32$c) where possible, and we do want
;; to be able to use those lemmas in a context where
;; (lofat-fs-p fat32$c) is known to be true without
;; allowing for the definition of fat32$c-p to be expanded.
;;
;; We're also disabling create-fat32$c because any time it gets
;; expanded in a subgoal there's trouble discharging it as well as writing it
;; out in full.
;;
;; Note, we're non-locally disabling these because we want them to be off by
;; default in other books.
(in-theory (disable fat32$c-p create-fat32$c))

(defthm
  bpb_bytspersec-of-update-data-regioni
  (equal
   (bpb_bytspersec (update-data-regioni i v fat32$c))
   (bpb_bytspersec fat32$c))
  :hints (("goal" :in-theory (enable update-data-regioni))))

(defthm
  bpb_secperclus-of-update-data-regioni
  (equal
   (bpb_secperclus (update-data-regioni i v fat32$c))
   (bpb_secperclus fat32$c))
  :hints (("goal" :in-theory (enable update-data-regioni))))

(defthm
  bpb_totsec32-of-update-data-regioni
  (equal
   (bpb_totsec32 (update-data-regioni i v fat32$c))
   (bpb_totsec32 fat32$c))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni bpb_totsec32))))

(defthm
  bpb_rsvdseccnt-of-update-data-regioni
  (equal
   (bpb_rsvdseccnt (update-data-regioni i v fat32$c))
   (bpb_rsvdseccnt fat32$c))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni bpb_rsvdseccnt))))

(defthm
  bpb_numfats-of-update-data-regioni
  (equal
   (bpb_numfats (update-data-regioni i v fat32$c))
   (bpb_numfats fat32$c))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni bpb_numfats))))

(defthm
  bpb_fatsz32-of-update-data-regioni
  (equal
   (bpb_fatsz32 (update-data-regioni i v fat32$c))
   (bpb_fatsz32 fat32$c))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni bpb_fatsz32))))

(defthm
  update-data-regioni-of-data-regioni
  (implies
   (and (fat32$c-p fat32$c)
        (< (nfix i)
           (data-region-length fat32$c)))
   (equal
    (update-data-regioni i (data-regioni i fat32$c)
                         fat32$c)
    fat32$c))
  :hints
  (("goal" :in-theory (enable fat32$c-p
                              data-regioni update-data-regioni
                              data-region-length))))

(defthm
  bpb_secperclus-of-resize-data-region
  (equal (bpb_secperclus (resize-data-region i fat32$c))
         (bpb_secperclus fat32$c))
  :hints
  (("goal"
    :in-theory (enable bpb_secperclus resize-data-region))))

(defthm
  bpb_bytspersec-of-resize-data-region
  (equal (bpb_bytspersec (resize-data-region i fat32$c))
         (bpb_bytspersec fat32$c))
  :hints
  (("goal"
    :in-theory (enable bpb_bytspersec resize-data-region))))

(defthm
  update-fati-of-fati-when-fat32$c-p
  (implies (and (fat32$c-p fat32$c)
                (< (nfix i)
                   (fat-length fat32$c)))
           (equal (update-fati i (fati i fat32$c)
                               fat32$c)
                  fat32$c))
  :hints
  (("goal" :in-theory (enable fati update-fati
                              fat-length fat32$c-p))))

(defmacro
    update-bpb_secperclus-macro
    (name stobj update-bpb_secperclus-of-name)
  `(defthm
     ,update-bpb_secperclus-of-name
     (equal
      (update-bpb_secperclus
       v1
       (,name v2 ,stobj))
      (,name
       v2
       (update-bpb_secperclus v1 ,stobj)))
     :hints (("goal" :in-theory (enable update-bpb_secperclus ,name)))))

(update-bpb_secperclus-macro update-bs_oemname fat32$c
                             update-bpb_secperclus-of-update-bs_oemname)

(update-bpb_secperclus-macro update-bs_jmpboot fat32$c
                             update-bpb_secperclus-of-update-bs_jmpboot)

(update-bpb_secperclus-macro update-bpb_bytspersec fat32$c
                             update-bpb_secperclus-of-update-bpb_bytspersec)

(update-bpb_secperclus-macro update-bpb_fatsz32 fat32$c
                             update-bpb_secperclus-of-update-bpb_fatsz32)

(update-bpb_secperclus-macro update-bpb_numfats fat32$c
                             update-bpb_secperclus-of-update-bpb_numfats)

(update-bpb_secperclus-macro update-bpb_rsvdseccnt fat32$c
                             update-bpb_secperclus-of-update-bpb_rsvdseccnt)

(defmacro
    update-bpb_rsvdseccnt-macro
    (name stobj update-bpb_rsvdseccnt-of-name)
  `(defthm
     ,update-bpb_rsvdseccnt-of-name
     (equal
      (update-bpb_rsvdseccnt
       v1
       (,name v2 ,stobj))
      (,name
       v2
       (update-bpb_rsvdseccnt v1 ,stobj)))
     :hints (("goal" :in-theory (enable update-bpb_rsvdseccnt ,name)))))

(update-bpb_rsvdseccnt-macro update-bs_oemname fat32$c
                             update-bpb_rsvdseccnt-of-update-bs_oemname)

(update-bpb_rsvdseccnt-macro update-bs_jmpboot fat32$c
                             update-bpb_rsvdseccnt-of-update-bs_jmpboot)

(update-bpb_rsvdseccnt-macro update-bpb_bytspersec fat32$c
                             update-bpb_rsvdseccnt-of-update-bpb_bytspersec)

(update-bpb_rsvdseccnt-macro update-bpb_fatsz32 fat32$c
                             update-bpb_rsvdseccnt-of-update-bpb_fatsz32)

(update-bpb_rsvdseccnt-macro update-bpb_numfats fat32$c
                             update-bpb_rsvdseccnt-of-update-bpb_numfats)

(defmacro
    update-bpb_numfats-macro
    (name stobj update-bpb_numfats-of-name)
  `(defthm
     ,update-bpb_numfats-of-name
     (equal
      (update-bpb_numfats
       v1
       (,name v2 ,stobj))
      (,name
       v2
       (update-bpb_numfats v1 ,stobj)))
     :hints (("goal" :in-theory (enable update-bpb_numfats ,name)))))

(update-bpb_numfats-macro update-bs_oemname fat32$c
                          update-bpb_numfats-of-update-bs_oemname)

(update-bpb_numfats-macro update-bs_jmpboot fat32$c
                          update-bpb_numfats-of-update-bs_jmpboot)

(update-bpb_numfats-macro update-bpb_bytspersec fat32$c
                          update-bpb_numfats-of-update-bpb_bytspersec)

(update-bpb_numfats-macro update-bpb_fatsz32 fat32$c
                          update-bpb_numfats-of-update-bpb_fatsz32)

(defmacro
    update-bpb_fatsz32-macro
    (name stobj update-bpb_fatsz32-of-name)
  `(defthm
     ,update-bpb_fatsz32-of-name
     (equal
      (update-bpb_fatsz32
       v1
       (,name v2 ,stobj))
      (,name
       v2
       (update-bpb_fatsz32 v1 ,stobj)))
     :hints (("goal" :in-theory (enable update-bpb_fatsz32 ,name)))))

(update-bpb_fatsz32-macro update-bs_oemname fat32$c
                          update-bpb_fatsz32-of-update-bs_oemname)

(update-bpb_fatsz32-macro update-bs_jmpboot fat32$c
                          update-bpb_fatsz32-of-update-bs_jmpboot)

(update-bpb_fatsz32-macro update-bpb_totsec32 fat32$c
                          update-bpb_fatsz32-of-update-bpb_totsec32)

(update-bpb_fatsz32-macro update-bpb_hiddsec fat32$c
                          update-bpb_fatsz32-of-update-bpb_hiddsec)

(update-bpb_fatsz32-macro update-bpb_numheads fat32$c
                          update-bpb_fatsz32-of-update-bpb_numheads)

(update-bpb_fatsz32-macro update-bpb_secpertrk fat32$c
                          update-bpb_fatsz32-of-update-bpb_secpertrk)

(update-bpb_fatsz32-macro update-bpb_fatsz16 fat32$c
                          update-bpb_fatsz32-of-update-bpb_fatsz16)

(update-bpb_fatsz32-macro update-bpb_media fat32$c
                          update-bpb_fatsz32-of-update-bpb_media)

(update-bpb_fatsz32-macro update-bpb_totsec16 fat32$c
                          update-bpb_fatsz32-of-update-bpb_totsec16)

(update-bpb_fatsz32-macro update-bpb_rootentcnt fat32$c
                          update-bpb_fatsz32-of-update-bpb_rootentcnt)

(update-bpb_fatsz32-macro update-bpb_bytspersec fat32$c
                          update-bpb_fatsz32-of-update-bpb_bytspersec)

(defmacro
    update-bpb_bytspersec-macro
    (name stobj update-bpb_bytspersec-of-name)
  `(defthm
     ,update-bpb_bytspersec-of-name
     (equal
      (update-bpb_bytspersec
       v1
       (,name v2 ,stobj))
      (,name
       v2
       (update-bpb_bytspersec v1 ,stobj)))
     :hints (("goal" :in-theory (enable update-bpb_bytspersec ,name)))))

(update-bpb_bytspersec-macro update-bs_oemname fat32$c
                             update-bpb_bytspersec-of-update-bs_oemname)

(update-bpb_bytspersec-macro update-bs_jmpboot fat32$c
                             update-bpb_bytspersec-of-update-bs_jmpboot)

(defthm
  fat32$c-p-of-resize-data-region
  (implies
   (fat32$c-p fat32$c)
   (fat32$c-p (resize-data-region i fat32$c)))
  :hints
  (("goal"
    :in-theory (enable fat32$c-p resize-data-region))))

(defthm
  fat32$c-p-of-update-fati
  (implies
   (fat32$c-p fat32$c)
   (equal (fat32$c-p (update-fati i v fat32$c))
          (and (fat32-entry-p v)
               (<= (nfix i)
                   (fat-length fat32$c)))))
  :hints
  (("goal" :in-theory (enable update-fati
                              fat32$c-p fat-length))))

(defthm update-fati-of-update-fati-coincident
  (equal (update-fati i v1 (update-fati i v2 fat32$c))
         (update-fati i v1 fat32$c))
  :hints (("goal" :in-theory (enable update-fati))))

(defthm update-fati-of-update-fati-disjoint
  (implies (not (equal (nfix i1) (nfix i2)))
           (equal (update-fati i1 v1 (update-fati i2 v2 fat32$c))
                  (update-fati i2 v2 (update-fati i1 v1 fat32$c))))
  :hints (("goal" :in-theory (e/d (update-fati) (update-nth)))))

(defthm
  fat-length-of-update-nth
  (implies
   (not (equal key *fati*))
   (equal (fat-length (update-nth key val fat32$c))
          (fat-length fat32$c)))
  :hints (("goal" :in-theory (enable fat-length))))

(defthm
  fat32$c-p-of-resize-fat
  (implies (fat32$c-p fat32$c)
           (fat32$c-p (resize-fat i fat32$c)))
  :hints
  (("goal" :in-theory (enable fat32$c-p resize-fat))))

(defthm
  fat-length-of-resize-data-region
  (equal (fat-length (resize-data-region i fat32$c))
         (fat-length fat32$c))
  :hints (("goal" :in-theory (enable resize-data-region))))

(defthm
  fat-length-of-update-data-regioni
  (equal
   (fat-length (update-data-regioni i v fat32$c))
   (fat-length fat32$c))
  :hints (("goal" :in-theory (enable update-data-regioni fat-length))))

(defthm
  nth-of-update-data-regioni
  (implies
   (not (equal (nfix n) *data-regioni*))
   (equal (nth n
               (update-data-regioni i v fat32$c))
          (nth n fat32$c)))
  :hints (("goal" :in-theory (enable update-data-regioni))))

(defthm
  resize-fat-of-fat-length-when-fat32$c-p
  (implies (fat32$c-p fat32$c)
           (equal (resize-fat (fat-length fat32$c)
                              fat32$c)
                  fat32$c))
  :hints
  (("goal" :in-theory (enable resize-fat
                              fat-length fat32$c-p)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (fat32$c-p fat32$c)
                  (equal i (fat-length fat32$c)))
             (equal (resize-fat i fat32$c)
                    fat32$c)))))

(defthm
  resize-data-region-of-data-region-length-when-fat32$c-p
  (implies
   (fat32$c-p fat32$c)
   (equal
    (resize-data-region (data-region-length fat32$c)
                        fat32$c)
    fat32$c))
  :hints
  (("goal"
    :in-theory (enable resize-data-region
                       data-region-length fat32$c-p)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (fat32$c-p fat32$c)
          (equal i (data-region-length fat32$c)))
     (equal (resize-data-region i fat32$c)
            fat32$c))
    :hints (("goal" :in-theory (enable resize-data-region))))))

(defthm
  nth-of-resize-data-region
  (implies (not (equal n *data-regioni*))
           (equal (nth n
                       (resize-data-region i fat32$c))
                  (nth n fat32$c)))
  :hints (("goal" :in-theory (enable resize-data-region))))

(defthm
  nth-of-resize-fat
  (equal (nth n (resize-fat i fat32$c))
         (if (not (equal n *fati*))
             (nth n fat32$c)
           (resize-list (nth *fati* fat32$c)
                        i '0)))
  :hints (("goal" :in-theory (enable resize-fat))))
