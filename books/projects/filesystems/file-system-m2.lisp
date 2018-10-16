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

;; This is to get the theorem about the nth element of a list of unsigned
;; bytes.
(local (include-book "std/typed-lists/integer-listp" :dir :system))

(encapsulate
  ()

  (local (include-book "std/basic/inductions" :dir :system))
  (defcong
    str::charlisteqv equal (chars=>nats x)
    1
    :hints
    (("goal" :in-theory (enable chars=>nats)
      :induct (cdr-cdr-induct x str::x-equiv)))))

(defthm consp-of-chars=>nats
  (iff (consp (chars=>nats chars))
       (consp chars))
  :hints (("goal" :in-theory (enable chars=>nats))))

(defthm consp-of-string=>nats
  (iff (consp (string=>nats string))
       (consp (explode string)))
  :hints (("goal" :in-theory (enable string=>nats))))

(defthm chars=>nats-of-make-list-ac
  (equal (chars=>nats (make-list-ac n val ac))
         (make-list-ac n (char-code val)
                       (chars=>nats ac)))
  :hints (("goal" :in-theory (enable chars=>nats))))

(defthm string=>nats-of-implode
  (implies (character-listp chars)
           (equal (string=>nats (implode chars))
                  (chars=>nats chars)))
  :hints (("goal" :in-theory (enable string=>nats))))

(defthmd chars=>nats-of-take
  (implies (<= (nfix n) (len chars))
           (equal (chars=>nats (take n chars))
                  (take n (chars=>nats chars))))
  :hints (("goal" :in-theory (enable chars=>nats))))

(defthmd chars=>nats-of-nthcdr
  (equal (chars=>nats (nthcdr n chars))
         (nthcdr n (chars=>nats chars)))
  :hints (("goal" :in-theory (enable chars=>nats nthcdr-of-nil))))

(defthmd chars=>nats-of-revappend
  (equal (chars=>nats (revappend x y))
         (revappend (chars=>nats x) (chars=>nats y)))
  :hints (("goal" :in-theory (enable chars=>nats))))

(defthm explode-of-nats=>string
  (equal (explode (nats=>string nats))
         (nats=>chars nats))
  :hints (("goal" :in-theory (enable nats=>string))))

(defthmd nats=>chars-of-revappend
  (equal (nats=>chars (revappend x y))
         (revappend (nats=>chars x) (nats=>chars y)))
  :hints (("goal" :in-theory (enable nats=>chars))))

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
                     update-bpb_totsec16 update-bs_volid)))

(local
 (in-theory (disable fati fat-length update-fati resize-fat
                     data-regioni data-region-length update-data-regioni
                     resize-data-region)))

(defmacro
  update-stobj-scalar-correctness
  (bit-width updater accessor
             stobj stobj-recogniser lemma-name1 lemma-name2 lemma-name3
             lemma-name4 lemma-name5 updater-of-updater updater-of-accessor)
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
       ,lemma-name5
       (equal (resize-data-region i (,updater v ,stobj))
              (,updater v (resize-data-region i ,stobj)))
       :hints
       (("goal" :in-theory (enable resize-data-region ,updater))))
     (defthm
       ,updater-of-updater
       (equal (,updater
               v1
               (,updater v2 fat32-in-memory))
              (,updater v1 fat32-in-memory))
       :hints (("goal" :in-theory (enable ,updater))))
     (defthm
       ,updater-of-accessor
       (implies (,stobj-recogniser ,stobj)
                (equal (,updater
                        (,accessor ,stobj)
                        ,stobj)
                       ,stobj))
       :hints (("goal" :in-theory (enable ,updater ,accessor)))))))

(update-stobj-scalar-correctness 16 update-bpb_rsvdseccnt bpb_rsvdseccnt
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_rsvdseccnt-correctness-1
                                 update-bpb_rsvdseccnt-correctness-2
                                 update-bpb_rsvdseccnt-correctness-3
                                 update-bpb_rsvdseccnt-correctness-4
                                 update-bpb_rsvdseccnt-correctness-5
                                 update-bpb_rsvdseccnt-of-update-bpb_rsvdseccnt
                                 update-bpb_rsvdseccnt-of-bpb_rsvdseccnt)

(update-stobj-scalar-correctness 8 update-bpb_secperclus bpb_secperclus
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_secperclus-correctness-1
                                 update-bpb_secperclus-correctness-2
                                 update-bpb_secperclus-correctness-3
                                 update-bpb_secperclus-correctness-4
                                 update-bpb_secperclus-correctness-5
                                 update-bpb_secperclus-of-update-bpb_secperclus
                                 update-bpb_secperclus-of-bpb_secperclus)

(update-stobj-scalar-correctness 16 update-bpb_bytspersec bpb_bytspersec
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_bytspersec-correctness-1
                                 update-bpb_bytspersec-correctness-2
                                 update-bpb_bytspersec-correctness-3
                                 update-bpb_bytspersec-correctness-4
                                 update-bpb_bytspersec-correctness-5
                                 update-bpb_bytspersec-of-update-bpb_bytspersec
                                 update-bpb_bytspersec-of-bpb_bytspersec)

(update-stobj-scalar-correctness 8 update-bpb_numfats bpb_numfats
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_numfats-correctness-1
                                 update-bpb_numfats-correctness-2
                                 update-bpb_numfats-correctness-3
                                 update-bpb_numfats-correctness-4
                                 update-bpb_numfats-correctness-5
                                 update-bpb_numfats-of-update-bpb_numfats
                                 update-bpb_numfats-of-bpb_numfats)

(update-stobj-scalar-correctness 32 update-bpb_rootclus bpb_rootclus
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_rootclus-correctness-1
                                 update-bpb_rootclus-correctness-2
                                 update-bpb_rootclus-correctness-3
                                 update-bpb_rootclus-correctness-4
                                 update-bpb_rootclus-correctness-5
                                 update-bpb_rootclus-of-update-bpb_rootclus
                                 update-bpb_rootclus-of-bpb_rootclus)

(update-stobj-scalar-correctness 16 update-bpb_fsinfo bpb_fsinfo
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fsinfo-correctness-1
                                 update-bpb_fsinfo-correctness-2
                                 update-bpb_fsinfo-correctness-3
                                 update-bpb_fsinfo-correctness-4
                                 update-bpb_fsinfo-correctness-5
                                 update-bpb_fsinfo-of-update-bpb_fsinfo
                                 update-bpb_fsinfo-of-bpb_fsinfo)

(update-stobj-scalar-correctness 16 update-bpb_bkbootsec bpb_bkbootsec
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_bkbootsec-correctness-1
                                 update-bpb_bkbootsec-correctness-2
                                 update-bpb_bkbootsec-correctness-3
                                 update-bpb_bkbootsec-correctness-4
                                 update-bpb_bkbootsec-correctness-5
                                 update-bpb_bkbootsec-of-update-bpb_bkbootsec
                                 update-bpb_bkbootsec-of-bpb_bkbootsec)

(update-stobj-scalar-correctness 8 update-bs_drvnum bs_drvnum
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_drvnum-correctness-1
                                 update-bs_drvnum-correctness-2
                                 update-bs_drvnum-correctness-3
                                 update-bs_drvnum-correctness-4
                                 update-bs_drvnum-correctness-5
                                 update-bs_drvnum-of-update-bs_drvnum
                                 update-bs_drvnum-of-bs_drvnum)

(update-stobj-scalar-correctness 8 update-bs_reserved1 bs_reserved1
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_reserved1-correctness-1
                                 update-bs_reserved1-correctness-2
                                 update-bs_reserved1-correctness-3
                                 update-bs_reserved1-correctness-4
                                 update-bs_reserved1-correctness-5
                                 update-bs_reserved1-of-update-bs_reserved1
                                 update-bs_reserved1-of-bs_reserved1)

(update-stobj-scalar-correctness 8 update-bs_bootsig bs_bootsig
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_bootsig-correctness-1
                                 update-bs_bootsig-correctness-2
                                 update-bs_bootsig-correctness-3
                                 update-bs_bootsig-correctness-4
                                 update-bs_bootsig-correctness-5
                                 update-bs_bootsig-of-update-bs_bootsig
                                 update-bs_bootsig-of-bs_bootsig)

(update-stobj-scalar-correctness 8 update-bpb_media bpb_media
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_media-correctness-1
                                 update-bpb_media-correctness-2
                                 update-bpb_media-correctness-3
                                 update-bpb_media-correctness-4
                                 update-bpb_media-correctness-5
                                 update-bpb_media-of-update-bpb_media
                                 update-bpb_media-of-bpb_media)

(update-stobj-scalar-correctness 8 update-bpb_fsver_minor bpb_fsver_minor
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fsver_minor-correctness-1
                                 update-bpb_fsver_minor-correctness-2
                                 update-bpb_fsver_minor-correctness-3
                                 update-bpb_fsver_minor-correctness-4
                                 update-bpb_fsver_minor-correctness-5
                                 update-bpb_fsver_minor-of-update-bpb_fsver_minor
                                 update-bpb_fsver_minor-of-bpb_fsver_minor)

(update-stobj-scalar-correctness 8 update-bpb_fsver_major bpb_fsver_major
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fsver_major-correctness-1
                                 update-bpb_fsver_major-correctness-2
                                 update-bpb_fsver_major-correctness-3
                                 update-bpb_fsver_major-correctness-4
                                 update-bpb_fsver_major-correctness-5
                                 update-bpb_fsver_major-of-update-bpb_fsver_major
                                 update-bpb_fsver_major-of-bpb_fsver_major)

(update-stobj-scalar-correctness 16 update-bpb_fatsz16 bpb_fatsz16
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fatsz16-correctness-1
                                 update-bpb_fatsz16-correctness-2
                                 update-bpb_fatsz16-correctness-3
                                 update-bpb_fatsz16-correctness-4
                                 update-bpb_fatsz16-correctness-5
                                 update-bpb_fatsz16-of-update-bpb_fatsz16
                                 update-bpb_fatsz16-of-bpb_fatsz16)

(update-stobj-scalar-correctness 16 update-bpb_secpertrk bpb_secpertrk
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_secpertrk-correctness-1
                                 update-bpb_secpertrk-correctness-2
                                 update-bpb_secpertrk-correctness-3
                                 update-bpb_secpertrk-correctness-4
                                 update-bpb_secpertrk-correctness-5
                                 update-bpb_secpertrk-of-update-bpb_secpertrk
                                 update-bpb_secpertrk-of-bpb_secpertrk)

(update-stobj-scalar-correctness 16 update-bpb_numheads bpb_numheads
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_numheads-correctness-1
                                 update-bpb_numheads-correctness-2
                                 update-bpb_numheads-correctness-3
                                 update-bpb_numheads-correctness-4
                                 update-bpb_numheads-correctness-5
                                 update-bpb_numheads-of-update-bpb_numheads
                                 update-bpb_numheads-of-bpb_numheads)

(update-stobj-scalar-correctness 16 update-bpb_extflags bpb_extflags
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_extflags-correctness-1
                                 update-bpb_extflags-correctness-2
                                 update-bpb_extflags-correctness-3
                                 update-bpb_extflags-correctness-4
                                 update-bpb_extflags-correctness-5
                                 update-bpb_extflags-of-update-bpb_extflags
                                 update-bpb_extflags-of-bpb_extflags)

(update-stobj-scalar-correctness 32 update-bpb_hiddsec bpb_hiddsec
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_hiddsec-correctness-1
                                 update-bpb_hiddsec-correctness-2
                                 update-bpb_hiddsec-correctness-3
                                 update-bpb_hiddsec-correctness-4
                                 update-bpb_hiddsec-correctness-5
                                 update-bpb_hiddsec-of-update-bpb_hiddsec
                                 update-bpb_hiddsec-of-bpb_hiddsec)

(update-stobj-scalar-correctness 32 update-bpb_totsec32 bpb_totsec32
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_totsec32-correctness-1
                                 update-bpb_totsec32-correctness-2
                                 update-bpb_totsec32-correctness-3
                                 update-bpb_totsec32-correctness-4
                                 update-bpb_totsec32-correctness-5
                                 update-bpb_totsec32-of-update-bpb_totsec32
                                 update-bpb_totsec32-of-bpb_totsec32)

(update-stobj-scalar-correctness 32 update-bpb_fatsz32 bpb_fatsz32
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_fatsz32-correctness-1
                                 update-bpb_fatsz32-correctness-2
                                 update-bpb_fatsz32-correctness-3
                                 update-bpb_fatsz32-correctness-4
                                 update-bpb_fatsz32-correctness-5
                                 update-bpb_fatsz32-of-update-bpb_fatsz32
                                 update-bpb_fatsz32-of-bpb_fatsz32)

(update-stobj-scalar-correctness 16 update-bpb_rootentcnt bpb_rootentcnt
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_rootentcnt-correctness-1
                                 update-bpb_rootentcnt-correctness-2
                                 update-bpb_rootentcnt-correctness-3
                                 update-bpb_rootentcnt-correctness-4
                                 update-bpb_rootentcnt-correctness-5
                                 update-bpb_rootentcnt-of-update-bpb_rootentcnt
                                 update-bpb_rootentcnt-of-bpb_rootentcnt)

(update-stobj-scalar-correctness 16 update-bpb_totsec16 bpb_totsec16
                                 fat32-in-memory fat32-in-memoryp
                                 update-bpb_totsec16-correctness-1
                                 update-bpb_totsec16-correctness-2
                                 update-bpb_totsec16-correctness-3
                                 update-bpb_totsec16-correctness-4
                                 update-bpb_totsec16-correctness-5
                                 update-bpb_totsec16-of-update-bpb_totsec16
                                 update-bpb_totsec16-of-bpb_totsec16)

(update-stobj-scalar-correctness 32 update-bs_volid bs_volid
                                 fat32-in-memory fat32-in-memoryp
                                 update-bs_volid-correctness-1
                                 update-bs_volid-correctness-2
                                 update-bs_volid-correctness-3
                                 update-bs_volid-correctness-4
                                 update-bs_volid-correctness-5
                                 update-bs_volid-of-update-bs_volid
                                 update-bs_volid-of-bs_volid)

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
       (>= (count-of-clusters fat32-in-memory)
           *ms-fat32-min-count-of-clusters*)
       (>= (bpb_rsvdseccnt fat32-in-memory) 1)
       (>= (bpb_numfats fat32-in-memory) 1)
       (>= (bpb_fatsz32 fat32-in-memory) 1)
       ;; this isn't in the spec, but clearly implied
       (>= (bpb_rootclus fat32-in-memory) *ms-first-data-cluster*)))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    compliant-fat32-in-memoryp-correctness-1
    (implies (compliant-fat32-in-memoryp fat32-in-memory)
             (and (fat32-in-memoryp fat32-in-memory)
                  (integerp (cluster-size fat32-in-memory))
                  (>= (cluster-size fat32-in-memory)
                      *ms-min-bytes-per-sector*)
                  (>= (count-of-clusters fat32-in-memory)
                      *ms-fat32-min-count-of-clusters*)
                  (>= (bpb_secperclus fat32-in-memory) 1)
                  (>= (bpb_rsvdseccnt fat32-in-memory) 1)
                  (>= (bpb_numfats fat32-in-memory) 1)
                  (>= (bpb_fatsz32 fat32-in-memory) 1)
                  (>= (bpb_rootclus fat32-in-memory)
                      *ms-first-data-cluster*)
                  (>= (bpb_bytspersec fat32-in-memory)
                      *ms-min-bytes-per-sector*)))
    :hints
    (("goal"
      :in-theory (e/d (compliant-fat32-in-memoryp cluster-size)
                      (fat32-in-memoryp))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (and (fat32-in-memoryp fat32-in-memory)
                    (integerp (cluster-size fat32-in-memory)))))
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
                    (>= (bpb_rsvdseccnt fat32-in-memory) 1)
                    (>= (bpb_numfats fat32-in-memory) 1)
                    (>= (bpb_fatsz32 fat32-in-memory) 1)
                    (>= (bpb_rootclus fat32-in-memory)
                        *ms-first-data-cluster*)
                    (>= (bpb_bytspersec fat32-in-memory)
                        *ms-min-bytes-per-sector*)))))))

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
        (delete-assoc 'update-bpb_fatsz32 *the-list*)
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
        (delete-assoc 'update-bpb_secperclus *the-list*)
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
        (delete-assoc 'update-bpb_rsvdseccnt *the-list*)
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
        (delete-assoc 'update-bpb_numfats *the-list*)
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
        (delete-assoc 'update-bpb_bytspersec *the-list*)
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
        (delete-assoc 'update-bpb_totsec32 *the-list*)
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
        (delete-assoc 'update-bpb_rootclus *the-list*)
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
  (equal (data-region-length (update-data-regioni i v fat32-in-memory))
         (max (data-region-length fat32-in-memory)
              (1+ (nfix i))))
  :hints (("goal" :in-theory (enable data-region-length update-data-regioni))))

(defthm
  data-region-length-of-resize-data-region
  (equal (data-region-length
          (resize-data-region i data-region32-in-memory))
         (nfix i))
  :hints (("goal" :in-theory (enable data-region-length
                                     resize-data-region))))

(defconst *initialbytcnt* 16)

(defmacro
  update-stobj-array
  (name array-length bit-width array-updater array-accessor constant
        stobj stobj-recogniser lemma-name1 lemma-name2 lemma-name3
        unsigned-byte-p-of-array-accessor lemma-name5 lemma-name6 lemma-name7
        lemma-name8 lemma-name9)
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
               (,stobj (,name (cdr v)
                              ,stobj)))
          ,stobj)))

     (defthm
       ,lemma-name1
       t
       :rule-classes
       ((:rewrite :corollary
                   (equal (bpb_secperclus (,name v ,stobj))
                          (bpb_secperclus fat32-in-memory))
                   :hints (("Goal" :in-theory (enable bpb_secperclus)) ))
        (:rewrite :corollary
                   (equal (bpb_rsvdseccnt (,name v ,stobj))
                          (bpb_rsvdseccnt fat32-in-memory))
                  :hints (("Goal" :in-theory (enable bpb_rsvdseccnt)) ))
        (:rewrite :corollary
                   (equal (bpb_numfats (,name v ,stobj))
                          (bpb_numfats fat32-in-memory))
                  :hints (("Goal" :in-theory (enable bpb_numfats)) ))
        (:rewrite :corollary
                   (equal (bpb_fatsz32 (,name v ,stobj))
                          (bpb_fatsz32 fat32-in-memory))
                  :hints (("Goal" :in-theory (enable bpb_fatsz32)) ))
        (:rewrite :corollary
                   (equal (bpb_bytspersec (,name v ,stobj))
                          (bpb_bytspersec fat32-in-memory))
                   :hints (("Goal" :in-theory (enable bpb_bytspersec)) ))
        (:rewrite :corollary
                   (equal (bpb_totsec32 (,name v ,stobj))
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
       :hints (("Goal" :in-theory (disable nth unsigned-byte-p)))
       :rule-classes
       (:rewrite
        (:rewrite
         :corollary
         (implies (and
                   (,stobj-recogniser ,stobj)
                   (< (nfix i) (,array-length ,stobj)))
                  (integerp (,array-accessor i ,stobj)))
         :hints (("Goal" :in-theory (disable nth fat32-in-memoryp))))
        (:linear
         :corollary
         (implies (and
                   (,stobj-recogniser ,stobj)
                   (< (nfix i) (,array-length ,stobj)))
                  (and
                   (<= 0 (,array-accessor i ,stobj))
                   (< (,array-accessor i ,stobj) ,upper-bound)))
         :hints (("Goal" :in-theory (disable nth fat32-in-memoryp))))))

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
               ,stobj))))))

(update-stobj-array
 update-bs_jmpboot bs_jmpboot-length 8
 update-bs_jmpbooti bs_jmpbooti *bs_jmpbooti*
 fat32-in-memory fat32-in-memoryp
 update-bs_jmpboot-correctness-1
 update-bs_jmpboot-correctness-2
 update-bs_jmpboot-correctness-3
 unsigned-byte-p-of-update-bs_jmpbooti
 update-bs_jmpboot-correctness-5
 update-bs_jmpboot-correctness-6
 update-bs_jmpboot-correctness-7
 update-bs_jmpboot-correctness-8
 update-bs_jmpboot-correctness-9)

(update-stobj-array
 update-bs_oemname bs_oemname-length 8
 update-bs_oemnamei bs_oemnamei *bs_oemnamei*
 fat32-in-memory fat32-in-memoryp
 update-bs_oemname-correctness-1
 update-bs_oemname-correctness-2
 update-bs_oemname-correctness-3
 unsigned-byte-p-of-update-bs_oemnamei
 update-bs_oemname-correctness-5
 update-bs_oemname-correctness-6
 update-bs_oemname-correctness-7
 update-bs_oemname-correctness-8
 update-bs_oemname-correctness-9)

(update-stobj-array
 update-bs_vollab bs_vollab-length 8
 update-bs_vollabi bs_vollabi *bs_vollabi*
 fat32-in-memory fat32-in-memoryp
 update-bs_vollab-correctness-1
 update-bs_vollab-correctness-2
 update-bs_vollab-correctness-3
 unsigned-byte-p-of-update-bs_vollabi
 update-bs_vollab-correctness-5
 update-bs_vollab-correctness-6
 update-bs_vollab-correctness-7
 update-bs_vollab-correctness-8
 update-bs_vollab-correctness-9)

(update-stobj-array
 update-bs_filsystype bs_filsystype-length 8
 update-bs_filsystypei bs_filsystypei *bs_filsystypei*
 fat32-in-memory fat32-in-memoryp
 update-bs_filsystype-correctness-1
 update-bs_filsystype-correctness-2
 update-bs_filsystype-correctness-3
 unsigned-byte-p-of-update-bs_filsystypei
 update-bs_filsystype-correctness-5
 update-bs_filsystype-correctness-6
 update-bs_filsystype-correctness-7
 update-bs_filsystype-correctness-8
 update-bs_filsystype-correctness-9)

(update-stobj-array
 update-bpb_reserved bpb_reserved-length 8
 update-bpb_reservedi bpb_reservedi *bpb_reservedi*
 fat32-in-memory fat32-in-memoryp
 update-bpb_reserved-correctness-1
 update-bpb_reserved-correctness-2
 update-bpb_reserved-correctness-3
 unsigned-byte-p-of-update-bpb_reservedi
 update-bpb_reserved-correctness-5
 update-bpb_reserved-correctness-6
 update-bpb_reserved-correctness-7
 update-bpb_reserved-correctness-8
 update-bpb_reserved-correctness-9)

(encapsulate
  ()

  (local
   (defthm update-multiple-elements-fn-correctness-1-lemma-1
     (implies (natp key)
              (equal (update-nth key (char-code x) l)
                     (append (take key l)
                             (list (char-code x))
                             (nthcdr (+ 1 key) l))))))

  (local
   (defthm update-multiple-elements-fn-correctness-1-lemma-2
     (equal (car (nthcdr n l)) (nth n l))))

  (local
   (defthm update-multiple-elements-fn-correctness-1-lemma-3
     (equal (take n (cdr l))
            (cdr (take (+ 1 n) l)))))

  (local
   (defthmd update-multiple-elements-fn-correctness-1-lemma-4
     (implies (not (zp n))
              (equal (cons (car l)
                           (append (cdr (take n l)) y))
                     (append (take n l) y)))))

  (local
   (defthm update-multiple-elements-fn-correctness-1-lemma-6
     (implies (not (zp n))
              (equal (cons (car l) (cdr (take n l)))
                     (take n l)))))

  (encapsulate
    (((update-single-element-fn * * fat32-in-memory)
      => fat32-in-memory)
     ((stobj-array-index) => *)
     ((stobj-array-length fat32-in-memory)
      => *)
     ((max-stobj-array-length) => *))

    (local
     (defund
       stobj-array-length (fat32-in-memory)
       (declare (xargs :guard (fat32-in-memoryp fat32-in-memory)
                       :stobjs fat32-in-memory))
       (data-region-length fat32-in-memory)))

    (local
     (defund
       update-single-element-fn
       (i v fat32-in-memory)
       (declare
        (xargs
         :stobjs fat32-in-memory
         :guard (and (fat32-in-memoryp fat32-in-memory)
                     (integerp i)
                     (<= 0 i)
                     (< i (stobj-array-length fat32-in-memory))
                     (unsigned-byte-p 8 v))
         :guard-hints (("Goal" :in-theory (enable
                                           stobj-array-length)))))
       (update-data-regioni i v fat32-in-memory)))

    (local (defund stobj-array-index () *data-regioni*))

    (local (defund max-stobj-array-length () *ms-max-data-region-size*))

    (local
     (defthm
       update-multiple-elements-fn-correctness-1-lemma-5
       (implies
        (and (natp pos)
             (integerp len)
             (< pos len))
        (equal
         (nthcdr
          len
          (nth (stobj-array-index)
               (update-single-element-fn pos v fat32-in-memory)))
         (nthcdr len
                 (nth (stobj-array-index)
                      fat32-in-memory))))
       :hints
       (("goal" :in-theory (enable update-single-element-fn))
        ("subgoal *1/3"
         :expand (update-data-regioni (+ -1 len)
                                      v fat32-in-memory)
         :in-theory (disable nthcdr-of-cdr)
         :use (:instance nthcdr-of-cdr
                         (x (nth *data-regioni* fat32-in-memory))
                         (i (+ -1 len)))))))

    (local
     (defthm
       update-multiple-elements-fn-correctness-1-lemma-7
       (implies
        (and (natp pos) (stringp str))
        (equal
         (take (+ 1 pos)
               (nth (stobj-array-index)
                    (update-single-element-fn
                     pos (char-code (nth pos (explode str)))
                     fat32-in-memory)))
         (append (take pos
                       (nth (stobj-array-index)
                            fat32-in-memory))
                 (list (char-code (nth pos (explode str)))))))
       :hints
       (("goal" :in-theory (enable update-data-regioni
                                   update-single-element-fn)))))

    (defthm
      update-multiple-elements-fn-correctness-1-lemma-8
      (implies
       (< (nfix i)
          (stobj-array-length fat32-in-memory))
       (equal (stobj-array-length
               (update-single-element-fn i v fat32-in-memory))
              (stobj-array-length fat32-in-memory)))
      :hints (("goal" :in-theory (enable update-single-element-fn
                                         stobj-array-length))))

    (defthm
      update-multiple-elements-fn-correctness-1-lemma-9
      (integerp (stobj-array-length fat32-in-memory))
      :hints (("goal" :in-theory (enable stobj-array-length))))

    (defthm
      update-multiple-elements-fn-correctness-1-lemma-10
      (implies
       (and (compliant-fat32-in-memoryp fat32-in-memory)
            (< i (stobj-array-length fat32-in-memory)))
       (equal (compliant-fat32-in-memoryp
               (update-single-element-fn i v fat32-in-memory))
              (unsigned-byte-p 8 v)))
      :hints (("goal" :in-theory (enable update-single-element-fn
                                         stobj-array-length))))

    (defthmd
      update-multiple-elements-fn-correctness-1-lemma-11
      (equal (update-single-element-fn i v fat32-in-memory)
             (update-nth-array (stobj-array-index)
                               i v fat32-in-memory))
      :hints (("goal" :in-theory (enable update-single-element-fn
                                         update-data-regioni))))

    (defthm
      update-multiple-elements-fn-correctness-1-lemma-12
      (integerp (max-stobj-array-length))
      :hints (("goal" :in-theory (enable stobj-array-length))))

    (defthm
      update-multiple-elements-fn-correctness-1-lemma-14
      (and
       (not (equal (stobj-array-index) *bpb_secperclus*))
       (not (equal (stobj-array-index) *bpb_rsvdseccnt*))
       (not (equal (stobj-array-index) *bpb_numfats*))
       (not (equal (stobj-array-index) *bpb_fatsz32*))
       (not (equal (stobj-array-index) *bpb_bytspersec*))
       (not (equal (stobj-array-index) *bpb_totsec32*)))
      :hints (("goal" :in-theory (enable stobj-array-length))))

    (defthm
      update-multiple-elements-fn-correctness-1-lemma-15
      (implies (and (fat32-in-memoryp fat32-in-memory)
                    (< i (stobj-array-length fat32-in-memory)))
               (equal
                (fat32-in-memoryp
                 (update-single-element-fn i v fat32-in-memory))
                (unsigned-byte-p 8 v)))
      :hints
      (("goal" :do-not-induct t
        :in-theory (e/d (stobj-array-length
                         update-multiple-elements-fn-correctness-1-lemma-11
                         data-region-length) (unsigned-byte-p)))))

    (defthm
      update-multiple-elements-fn-correctness-1-lemma-16
      (<= 0 (stobj-array-length fat32-in-memory))
      :rule-classes :linear
      :hints (("goal" :in-theory (enable stobj-array-length)))))

  (defun
    update-multiple-elements-fn
    (fat32-in-memory str len pos)
    (declare
     (xargs
      :guard (and (stringp str)
                  (natp len)
                  (natp pos)
                  (<= pos len)
                  (= len (length str))
                  (<= len
                      (stobj-array-length fat32-in-memory))
                  (<= (stobj-array-length fat32-in-memory)
                      (max-stobj-array-length)))
      :guard-hints
      (("goal"
        :in-theory (e/d (data-region-length update-data-regioni)
                        (fat32-in-memoryp))))
      :stobjs fat32-in-memory
      :measure (nfix (- len pos))))
    (if
     (zp (- len pos))
     fat32-in-memory
     (b*
         ((ch (char str pos))
          (ch-byte (char-code ch))
          (pos+1 (1+ pos))
          (fat32-in-memory
           (update-single-element-fn pos ch-byte fat32-in-memory)))
       (update-multiple-elements-fn
        fat32-in-memory str len pos+1))))

  (local
   (defthm
     update-multiple-elements-fn-correctness-1-lemma-13
     t
     :rule-classes
     ((:rewrite
       :corollary
       (equal (bpb_secperclus
               (update-single-element-fn i v fat32-in-memory))
              (bpb_secperclus fat32-in-memory))
       :hints
       (("goal"
         :in-theory
         (enable
          update-multiple-elements-fn-correctness-1-lemma-11
          bpb_secperclus))))
      (:rewrite
       :corollary
       (equal (bpb_rsvdseccnt
               (update-single-element-fn i v fat32-in-memory))
              (bpb_rsvdseccnt fat32-in-memory))
       :hints
       (("goal"
         :in-theory
         (enable
          update-multiple-elements-fn-correctness-1-lemma-11
          bpb_rsvdseccnt))))
      (:rewrite
       :corollary
       (equal (bpb_numfats
               (update-single-element-fn i v fat32-in-memory))
              (bpb_numfats fat32-in-memory))
       :hints
       (("goal"
         :in-theory
         (enable
          update-multiple-elements-fn-correctness-1-lemma-11
          bpb_numfats))))
      (:rewrite
       :corollary
       (equal (bpb_fatsz32
               (update-single-element-fn i v fat32-in-memory))
              (bpb_fatsz32 fat32-in-memory))
       :hints
       (("goal"
         :in-theory
         (enable
          update-multiple-elements-fn-correctness-1-lemma-11
          bpb_fatsz32))))
      (:rewrite
       :corollary
       (equal (bpb_bytspersec
               (update-single-element-fn i v fat32-in-memory))
              (bpb_bytspersec fat32-in-memory))
       :hints
       (("goal"
         :in-theory
         (enable
          update-multiple-elements-fn-correctness-1-lemma-11
          bpb_bytspersec))))
      (:rewrite
       :corollary
       (equal (bpb_totsec32
               (update-single-element-fn i v fat32-in-memory))
              (bpb_totsec32 fat32-in-memory))
       :hints
       (("goal"
         :in-theory
         (enable
          update-multiple-elements-fn-correctness-1-lemma-11
          bpb_totsec32)))))))

  (local (include-book "std/lists/nthcdr" :dir :system))

  (defthmd
    update-multiple-elements-fn-correctness-1
    (implies
     (and (natp pos)
          (natp len)
          (< pos len)
          (<= len
              (stobj-array-length fat32-in-memory))
          (compliant-fat32-in-memoryp fat32-in-memory)
          (stringp str)
          (<= len (length str)))
     (equal
      (update-multiple-elements-fn fat32-in-memory str len pos)
      (update-nth (stobj-array-index)
                  (append (take pos
                                (nth (stobj-array-index)
                                     fat32-in-memory))
                          (string=>nats (subseq str pos len))
                          (nthcdr len
                                  (nth (stobj-array-index)
                                       fat32-in-memory)))
                  fat32-in-memory)))
    :hints
    (("goal"
      :in-theory (disable fat32-in-memoryp)
      :induct
      (update-multiple-elements-fn fat32-in-memory str len pos))
     ("subgoal *1/7''"
      :in-theory (e/d (update-multiple-elements-fn-correctness-1-lemma-4
                       string=>nats chars=>nats)
                      (append-of-cons))
      :expand
      ((:free (v fat32-in-memory)
              (update-data-regioni 0 v fat32-in-memory))))
     ("subgoal *1/7.2"
      :expand (update-data-regioni
               pos (char-code (nth pos (explode str)))
               fat32-in-memory))
     ("subgoal *1/4'''"
      :expand
      ((string=>nats
        (implode (list (nth (+ -1 len) (explode str)))))
       (update-data-regioni
        (+ -1 len)
        (char-code (nth (+ -1 len) (explode str)))
        fat32-in-memory)))
     ("subgoal *1/2" :in-theory (enable string=>nats))
     ("subgoal *1/2.3'''"
      :in-theory
      (e/d (update-multiple-elements-fn-correctness-1-lemma-11)
           (update-multiple-elements-fn-correctness-1-lemma-1))
      :use (:instance
            update-multiple-elements-fn-correctness-1-lemma-1
            (key (+ -1 len))
            (x (nth (+ -1 len) (explode str)))
            (l (nth (stobj-array-index)
                    fat32-in-memory))))
     ("subgoal *1/2.2"
      :in-theory (e/d (update-multiple-elements-fn-correctness-1-lemma-11
                       chars=>nats)
                      (nthcdr-of-cdr))
      :use (:instance nthcdr-of-cdr (i (+ -1 len))
                      (x (nth (stobj-array-index)
                              fat32-in-memory)))
      :expand
      ((append (chars=>nats (take (+ len (- pos))
                                  (nthcdr pos (explode str))))
               (nthcdr len
                       (nth (stobj-array-index)
                            fat32-in-memory)))
       (nthcdr len
               (nth (stobj-array-index)
                    fat32-in-memory))))
     ("subgoal *1/1'''"
      :in-theory (enable data-region-length fat32-in-memoryp))))

  (defthm
    update-multiple-elements-fn-correctness-2
    (and
     (equal (bpb_secperclus
             (update-multiple-elements-fn
              fat32-in-memory str len pos))
            (bpb_secperclus fat32-in-memory))
     (equal (bpb_rsvdseccnt
             (update-multiple-elements-fn
              fat32-in-memory str len pos))
            (bpb_rsvdseccnt fat32-in-memory))
     (equal (bpb_numfats
             (update-multiple-elements-fn
              fat32-in-memory str len pos))
            (bpb_numfats fat32-in-memory))
     (equal (bpb_fatsz32
             (update-multiple-elements-fn
              fat32-in-memory str len pos))
            (bpb_fatsz32 fat32-in-memory))
     (equal (bpb_bytspersec
             (update-multiple-elements-fn
              fat32-in-memory str len pos))
            (bpb_bytspersec fat32-in-memory))
     (equal (bpb_totsec32
             (update-multiple-elements-fn
              fat32-in-memory str len pos))
            (bpb_totsec32 fat32-in-memory))))

  (defthm
    update-multiple-elements-fn-correctness-3
    (implies
     (and (fat32-in-memoryp fat32-in-memory)
          (natp pos)
          (integerp len)
          (<= pos len)
          (<= len
              (stobj-array-length fat32-in-memory)))
     (fat32-in-memoryp
      (update-multiple-elements-fn fat32-in-memory str len pos)))
    :hints (("goal" :in-theory (disable fat32-in-memoryp)))))

(defthm
  compliant-fat32-in-memoryp-of-update-bs_oemnamei
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (< i (bs_oemname-length fat32-in-memory)))
           (equal
            (compliant-fat32-in-memoryp
             (update-bs_oemnamei i v fat32-in-memory))
            (unsigned-byte-p 8 v)))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (compliant-fat32-in-memoryp
                     update-bs_oemnamei
                     bs_oemname-length count-of-clusters)
                    (floor)))))

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
       ("subgoal 7" :in-theory (disable unsigned-byte-p-of-nth-when-unsigned-byte-p)
        :use ((:instance
               unsigned-byte-p-of-nth-when-unsigned-byte-p
               (n 13)
               (l (get-initial-bytes str))
               (bits 8))
              (:instance unsigned-byte-p-forward-to-nonnegative-integerp
                         (n bits)
                         (x (nth 13 (get-initial-bytes str))))))
       ("subgoal 6" :in-theory (disable unsigned-byte-p-of-nth-when-unsigned-byte-p)
        :use (:instance
              unsigned-byte-p-of-nth-when-unsigned-byte-p
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
         ;; least 1 sector if we're going to have at least 65536 clusters of
         ;; data, as required by the FAT specification at the place where it
         ;; specifies how to distinguish between volumes formatted with FAT12,
         ;; FAT16 and FAT32.
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
  bpb_rsvdseccnt-of-update-data-regioni
  (equal
   (bpb_rsvdseccnt (update-data-regioni i v fat32-in-memory))
   (bpb_rsvdseccnt fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni bpb_rsvdseccnt))))

(defthm
  bpb_numfats-of-update-data-regioni
  (equal
   (bpb_numfats (update-data-regioni i v fat32-in-memory))
   (bpb_numfats fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni bpb_numfats))))

(defthm
  bpb_fatsz32-of-update-data-regioni
  (equal
   (bpb_fatsz32 (update-data-regioni i v fat32-in-memory))
   (bpb_fatsz32 fat32-in-memory))
  :hints
  (("goal"
    :in-theory (enable update-data-regioni bpb_fatsz32))))

(encapsulate
  ()

  (local
   (defthm fat32-in-memory-of-update-data-region
     (implies (and (fat32-in-memoryp fat32-in-memory)
                   (< i (data-region-length fat32-in-memory)))
              (equal (fat32-in-memoryp (update-data-regioni i v
                                                           fat32-in-memory))
                     (unsigned-byte-p 8 v)))
     :hints (("Goal" :in-theory (enable update-data-regioni data-region-length)))))

  (defthmd
    update-data-region-correctness-1
    (implies
     (and (natp pos)
          (natp len)
          (< pos len)
          (<= len
              (data-region-length fat32-in-memory))
          (compliant-fat32-in-memoryp fat32-in-memory)
          (stringp str)
          (<= len (length str)))
     (equal
      (update-data-region fat32-in-memory str len pos)
      (update-nth
       *data-regioni*
       (append (take pos
                     (nth *data-regioni* fat32-in-memory))
               (string=>nats (subseq str pos len))
               (nthcdr len
                       (nth *data-regioni* fat32-in-memory)))
       fat32-in-memory)))
    :hints
    (("Goal"
      :use
      ((:functional-instance
        update-multiple-elements-fn-correctness-1
        ;; Instantiate the generic functions:
        (update-single-element-fn update-data-regioni)
        (stobj-array-index (lambda () *data-regioni*))
        (stobj-array-length data-region-length)
        (max-stobj-array-length (lambda () *ms-max-data-region-size*))
        ;; Instantiate the other relevant functions:
        (update-multiple-elements-fn update-data-region)))
      :in-theory (disable fat32-in-memoryp))
     ("Subgoal 4"
      :in-theory (enable update-data-regioni)))))

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
    (("goal" :in-theory (enable take-redefinition
                                revappend-removal data-regioni))
     ("subgoal *1/2.4'''" :expand (repeat (+ -1 len) nil))
     ("subgoal *1/2.1'''" :expand (repeat (+ -1 len) nil))))

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

  (defund
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

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    reserved-area-string-guard-lemma-1
    (implies (compliant-fat32-in-memoryp fat32-in-memory)
             (natp (- (* (bpb_bytspersec fat32-in-memory)
                         (bpb_rsvdseccnt fat32-in-memory))
                      90)))
    :rule-classes
    ((:linear
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (<= 90
                   (* (bpb_bytspersec fat32-in-memory)
                      (bpb_rsvdseccnt fat32-in-memory)))))
     (:rewrite
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (integerp (* (bpb_bytspersec fat32-in-memory)
                            (bpb_rsvdseccnt fat32-in-memory)))))
     (:rewrite
      :corollary
      (implies (compliant-fat32-in-memoryp fat32-in-memory)
               (integerp (- (* (bpb_bytspersec fat32-in-memory)
                               (bpb_rsvdseccnt fat32-in-memory)))))))
    :hints (("goal" :in-theory (e/d (compliant-fat32-in-memoryp)
                                    (fat32-in-memoryp))))))

(defthm
  reserved-area-string-guard-lemma-2
  (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                (natp i)
                (< i (fat-length fat32-in-memory)))
           (and (integerp (fati i fat32-in-memory))
                (<= 0 (fati i fat32-in-memory))
                (< (fati i fat32-in-memory) 4294967296)))
  :rule-classes
  ((:rewrite
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (fat-length fat32-in-memory)))
                        (integerp (fati i fat32-in-memory))))
   (:linear
    :corollary (implies (and (compliant-fat32-in-memoryp fat32-in-memory)
                             (natp i)
                             (< i (fat-length fat32-in-memory)))
                        (and (<= 0 (fati i fat32-in-memory))
                             (< (fati i fat32-in-memory)
                                4294967296)))))
  :hints
  (("goal"
    :in-theory
    (e/d (compliant-fat32-in-memoryp fat32-entry-p)
         (fati fat32-in-memoryp
               fati-when-compliant-fat32-in-memoryp))
    :use fati-when-compliant-fat32-in-memoryp)))

(encapsulate
  ()

  (local (include-book "ihs/logops-lemmas" :dir :system))

  (local
   (defthm
     reserved-area-string-guard-lemma-3
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

  (defund reserved-area-chars (fat32-in-memory)
    (declare (xargs :stobjs fat32-in-memory
                    :guard (compliant-fat32-in-memoryp fat32-in-memory)
                    :guard-debug t
                    :guard-hints (("Goal"
                                   :do-not-induct t
                                   :in-theory (disable loghead logtail
                                                       bs_vollabi
                                                       bs_jmpbooti
                                                       bs_oemnamei
                                                       bs_filsystypei
                                                       bpb_reservedi
                                                       reserved-area-string-guard-lemma-2)
                                   :use
                                   reserved-area-string-guard-lemma-2))))
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
      :initial-element (code-char 0)))))

(defthm character-listp-of-reserved-area-chars
  (character-listp (reserved-area-chars fat32-in-memory))
  :hints (("Goal" :in-theory (enable reserved-area-chars))))

(defthm
  len-of-reserved-area-chars
  (implies
   (compliant-fat32-in-memoryp fat32-in-memory)
   (equal (len (reserved-area-chars fat32-in-memory))
          (* (bpb_rsvdseccnt fat32-in-memory)
             (bpb_bytspersec fat32-in-memory))))
  :hints (("goal" :in-theory (e/d (reserved-area-chars) (loghead logtail)))))

(defund
  reserved-area-string (fat32-in-memory)
  (declare
   (xargs :stobjs fat32-in-memory
          :guard (compliant-fat32-in-memoryp fat32-in-memory)))
  (implode (reserved-area-chars fat32-in-memory)))

(defthm
  length-of-reserved-area-string
  (implies
   (compliant-fat32-in-memoryp fat32-in-memory)
   (equal (len (explode (reserved-area-string fat32-in-memory)))
          (* (bpb_rsvdseccnt fat32-in-memory)
             (bpb_bytspersec fat32-in-memory))))
  :hints (("goal" :in-theory (enable reserved-area-string))))

;; This seems like the only way...
;; There is an automatic way to do this proof, but I can't recall it.
(defthm
  nth-of-explode-of-reserved-area-string
  (equal
   (nth n
        (explode (reserved-area-string fat32-in-memory)))
   (nth
    n
    (append
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
           (code-char (loghead 8 (bpb_hiddsec fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bpb_hiddsec fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bpb_hiddsec fat32-in-memory))))
           (code-char (logtail 24 (bpb_hiddsec fat32-in-memory)))
           (code-char (loghead 8 (bpb_totsec32 fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bpb_totsec32 fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bpb_totsec32 fat32-in-memory))))
           (code-char (logtail 24 (bpb_totsec32 fat32-in-memory)))
           (code-char (loghead 8 (bpb_fatsz32 fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bpb_fatsz32 fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bpb_fatsz32 fat32-in-memory))))
           (code-char (logtail 24 (bpb_fatsz32 fat32-in-memory)))
           (code-char (loghead 8 (bpb_extflags fat32-in-memory)))
           (code-char (logtail 8 (bpb_extflags fat32-in-memory)))
           (code-char (bpb_fsver_minor fat32-in-memory))
           (code-char (bpb_fsver_major fat32-in-memory))
           (code-char (loghead 8 (bpb_rootclus fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bpb_rootclus fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bpb_rootclus fat32-in-memory))))
           (code-char (logtail 24 (bpb_rootclus fat32-in-memory)))
           (code-char (loghead 8 (bpb_fsinfo fat32-in-memory)))
           (code-char (logtail 8 (bpb_fsinfo fat32-in-memory)))
           (code-char (loghead 8 (bpb_bkbootsec fat32-in-memory)))
           (code-char (logtail 8 (bpb_bkbootsec fat32-in-memory))))
     (list (code-char (bpb_reservedi 0 fat32-in-memory))
           (code-char (bpb_reservedi 1 fat32-in-memory))
           (code-char (bpb_reservedi 2 fat32-in-memory))
           (code-char (bpb_reservedi 3 fat32-in-memory))
           (code-char (bpb_reservedi 4 fat32-in-memory))
           (code-char (bpb_reservedi 5 fat32-in-memory))
           (code-char (bpb_reservedi 6 fat32-in-memory))
           (code-char (bpb_reservedi 7 fat32-in-memory))
           (code-char (bpb_reservedi 8 fat32-in-memory))
           (code-char (bpb_reservedi 9 fat32-in-memory))
           (code-char (bpb_reservedi 10 fat32-in-memory))
           (code-char (bpb_reservedi 11 fat32-in-memory)))
     (list (code-char (bs_drvnum fat32-in-memory))
           (code-char (bs_reserved1 fat32-in-memory))
           (code-char (bs_bootsig fat32-in-memory))
           (code-char (loghead 8 (bs_volid fat32-in-memory)))
           (code-char (loghead 8
                               (logtail 8 (bs_volid fat32-in-memory))))
           (code-char (loghead 8
                               (logtail 16 (bs_volid fat32-in-memory))))
           (code-char (logtail 24 (bs_volid fat32-in-memory))))
     (list (code-char (bs_vollabi 0 fat32-in-memory))
           (code-char (bs_vollabi 1 fat32-in-memory))
           (code-char (bs_vollabi 2 fat32-in-memory))
           (code-char (bs_vollabi 3 fat32-in-memory))
           (code-char (bs_vollabi 4 fat32-in-memory))
           (code-char (bs_vollabi 5 fat32-in-memory))
           (code-char (bs_vollabi 6 fat32-in-memory))
           (code-char (bs_vollabi 7 fat32-in-memory))
           (code-char (bs_vollabi 8 fat32-in-memory))
           (code-char (bs_vollabi 9 fat32-in-memory))
           (code-char (bs_vollabi 10 fat32-in-memory)))
     (list (code-char (bs_filsystypei 0 fat32-in-memory))
           (code-char (bs_filsystypei 1 fat32-in-memory))
           (code-char (bs_filsystypei 2 fat32-in-memory))
           (code-char (bs_filsystypei 3 fat32-in-memory))
           (code-char (bs_filsystypei 4 fat32-in-memory))
           (code-char (bs_filsystypei 5 fat32-in-memory))
           (code-char (bs_filsystypei 6 fat32-in-memory))
           (code-char (bs_filsystypei 7 fat32-in-memory)))
     (make-list (- (* (bpb_rsvdseccnt fat32-in-memory)
                      (bpb_bytspersec fat32-in-memory))
                   90)
                :initial-element (code-char 0)))))
  :instructions ((:in-theory (disable loghead logtail))
                 (:dive 1 2 1)
                 :x
                 :up (:rewrite str::explode-of-implode)
                 :s (:rewrite already-a-character-list)
                 :x :top
                 :bash :bash))

;; A bit of explanation is in order here - this function recurs on n, which is
;; instantiated with (bpb_numfats fat32-in-memory) in
;; fat32-in-memory-to-string. stobj-fa-table-to-string, in contrast, generates
;; one copy of the FAT string from the fat32-in-memory instance, and does all
;; the part-select heavy lifting.
(defund
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

(defthm
  length-of-stobj-fa-table-to-string
  (equal
   (len
    (explode (stobj-fa-table-to-string fat32-in-memory length)))
   (* (nfix length) 4))
  :hints (("goal" :in-theory (e/d (stobj-fa-table-to-string) (loghead logtail)))))

(defthm
  length-of-make-fat-string-ac
  (equal
   (len (explode (make-fat-string-ac n fat32-in-memory ac)))
   (+ (* (nfix n)
         (fat-length fat32-in-memory)
         4)
      (len (explode ac))))
  :hints (("Goal" :in-theory (enable make-fat-string-ac))))

(defthm
  len-of-get-dir-ent-helper
  (equal (len (get-dir-ent-helper fat32-in-memory
                                  data-region-index len ac))
         (+ (nfix len) (len ac))))

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

(defthm
  length-of-fat32-in-memory-to-string-lemma-1
  (implies (compliant-fat32-in-memoryp fat32-in-memory)
           (equal (nfix (bpb_numfats fat32-in-memory))
                  (bpb_numfats fat32-in-memory)))
  :hints (("goal" :in-theory (enable compliant-fat32-in-memoryp
                                     bpb_numfats))))

(defthm
  length-of-fat32-in-memory-to-string-lemma-2
  (implies (compliant-fat32-in-memoryp fat32-in-memory)
           (equal (nfix (data-region-length fat32-in-memory))
                  (data-region-length fat32-in-memory)))
  :hints (("goal" :in-theory (enable compliant-fat32-in-memoryp
                                     bpb_numfats))))

(defthm
  length-of-fat32-in-memory-to-string
  (implies
   (compliant-fat32-in-memoryp fat32-in-memory)
   (equal
    (len
     (explode (fat32-in-memory-to-string fat32-in-memory)))
    (+ (* (bpb_rsvdseccnt fat32-in-memory)
          (bpb_bytspersec fat32-in-memory))
       (* (bpb_numfats fat32-in-memory)
          (fat-length fat32-in-memory)
          4)
       (data-region-length fat32-in-memory))))
  :hints
  (("goal" :in-theory (e/d (fat32-in-memory-to-string) (nfix)))))

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

(update-bpb_secperclus-macro update-bs_oemname fat32-in-memory
                             update-bpb_secperclus-of-update-bs_oemname)

(update-bpb_secperclus-macro update-bs_jmpboot fat32-in-memory
                             update-bpb_secperclus-of-update-bs_jmpboot)

(update-bpb_secperclus-macro update-bpb_bytspersec fat32-in-memory
                             update-bpb_secperclus-of-update-bpb_bytspersec)

(update-bpb_secperclus-macro update-bpb_fatsz32 fat32-in-memory
                             update-bpb_secperclus-of-update-bpb_fatsz32)

(update-bpb_secperclus-macro update-bpb_numfats fat32-in-memory
                             update-bpb_secperclus-of-update-bpb_numfats)

(update-bpb_secperclus-macro update-bpb_rsvdseccnt fat32-in-memory
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

(update-bpb_rsvdseccnt-macro update-bs_oemname fat32-in-memory
                             update-bpb_rsvdseccnt-of-update-bs_oemname)

(update-bpb_rsvdseccnt-macro update-bs_jmpboot fat32-in-memory
                             update-bpb_rsvdseccnt-of-update-bs_jmpboot)

(update-bpb_rsvdseccnt-macro update-bpb_bytspersec fat32-in-memory
                             update-bpb_rsvdseccnt-of-update-bpb_bytspersec)

(update-bpb_rsvdseccnt-macro update-bpb_fatsz32 fat32-in-memory
                             update-bpb_rsvdseccnt-of-update-bpb_fatsz32)

(update-bpb_rsvdseccnt-macro update-bpb_numfats fat32-in-memory
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

(update-bpb_numfats-macro update-bs_oemname fat32-in-memory
                          update-bpb_numfats-of-update-bs_oemname)

(update-bpb_numfats-macro update-bs_jmpboot fat32-in-memory
                          update-bpb_numfats-of-update-bs_jmpboot)

(update-bpb_numfats-macro update-bpb_bytspersec fat32-in-memory
                          update-bpb_numfats-of-update-bpb_bytspersec)

(update-bpb_numfats-macro update-bpb_fatsz32 fat32-in-memory
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

(update-bpb_fatsz32-macro update-bs_oemname fat32-in-memory
                          update-bpb_fatsz32-of-update-bs_oemname)

(update-bpb_fatsz32-macro update-bs_jmpboot fat32-in-memory
                          update-bpb_fatsz32-of-update-bs_jmpboot)

(update-bpb_fatsz32-macro update-bpb_totsec32 fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_totsec32)

(update-bpb_fatsz32-macro update-bpb_hiddsec fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_hiddsec)

(update-bpb_fatsz32-macro update-bpb_numheads fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_numheads)

(update-bpb_fatsz32-macro update-bpb_secpertrk fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_secpertrk)

(update-bpb_fatsz32-macro update-bpb_fatsz16 fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_fatsz16)

(update-bpb_fatsz32-macro update-bpb_media fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_media)

(update-bpb_fatsz32-macro update-bpb_totsec16 fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_totsec16)

(update-bpb_fatsz32-macro update-bpb_rootentcnt fat32-in-memory
                          update-bpb_fatsz32-of-update-bpb_rootentcnt)

(update-bpb_fatsz32-macro update-bpb_bytspersec fat32-in-memory
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

(update-bpb_bytspersec-macro update-bs_oemname fat32-in-memory
                             update-bpb_bytspersec-of-update-bs_oemname)

(update-bpb_bytspersec-macro update-bs_jmpboot fat32-in-memory
                             update-bpb_bytspersec-of-update-bs_jmpboot)

(defthm
  fat32-in-memory-to-string-inversion-lemma-2
  (implies
   (stringp str)
   (iff
    (consp (get-remaining-rsvdbyts str))
    (not (zp
          (+ -16
             (* (combine16u (nth 12 (get-initial-bytes str))
                            (nth 11 (get-initial-bytes str)))
                (combine16u (nth 15 (get-initial-bytes str))
                            (nth 14 (get-initial-bytes str)))))))))
  :hints (("goal" :in-theory (disable
                              get-remaining-rsvdbyts-correctness-1)
           :use get-remaining-rsvdbyts-correctness-1
           :expand (len (get-remaining-rsvdbyts str)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-3
    (implies (fat32-in-memoryp fat32-in-memory)
             (>= (+ (data-region-length fat32-in-memory)
                    (* (bpb_bytspersec fat32-in-memory)
                       (bpb_rsvdseccnt fat32-in-memory))
                    (* (bpb_numfats fat32-in-memory)
                       4 (fat-length fat32-in-memory)))
                 (* (bpb_bytspersec fat32-in-memory)
                    (bpb_rsvdseccnt fat32-in-memory))))
    :hints (("goal" :in-theory (enable bpb_numfats)) )
    :rule-classes :linear))

(encapsulate
  ()

  (local
   (in-theory (e/d (fat32-in-memory-to-string get-initial-bytes get-remaining-rsvdbyts)
                   (logtail loghead fat32-in-memoryp floor
                            stobj-fa-table-to-string make-fat-string-ac))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-4
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth 11
            (get-initial-bytes
             (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_bytspersec fat32-in-memory)))
      (equal
       (nth 12
            (get-initial-bytes
             (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_bytspersec fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-5
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth 13
           (get-initial-bytes
            (fat32-in-memory-to-string fat32-in-memory)))
      (bpb_secperclus fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-6
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth 14
            (get-initial-bytes
             (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_rsvdseccnt fat32-in-memory)))
      (equal
       (nth 15
            (get-initial-bytes
             (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_rsvdseccnt fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-7
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth 0
           (get-remaining-rsvdbyts
            (fat32-in-memory-to-string fat32-in-memory)))
      (bpb_numfats fat32-in-memory)))
    :hints
    (("goal" :in-theory (enable string=>nats))
     ("subgoal 10''"
      :in-theory (disable nth-of-chars=>nats)
      :use
      (:instance
       nth-of-chars=>nats (i 0)
       (chars
        (take
         (+ -16
            (* (bpb_bytspersec fat32-in-memory)
               (bpb_rsvdseccnt fat32-in-memory)))
         (nthcdr
          16
          (append
           (explode (reserved-area-string fat32-in-memory))
           (explode
            (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                fat32-in-memory ""))
           (revappend
            (explode
             (nats=>string
              (revappend
               (take (data-region-length fat32-in-memory)
                     (nth *data-regioni* fat32-in-memory))
               nil)))
            nil)))))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-8
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        1
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_rootentcnt fat32-in-memory)))
      (equal
       (nth
        2
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_rootentcnt fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-9
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        3
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_totsec16 fat32-in-memory)))
      (equal
       (nth
        4
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_totsec16 fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-10
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth
       5
       (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
      (bpb_media fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-11
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        6
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_fatsz16 fat32-in-memory)))
      (equal
       (nth
        7
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_fatsz16 fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-12
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        8
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_secpertrk fat32-in-memory)))
      (equal
       (nth
        9
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_secpertrk fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-13
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        10
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_numheads fat32-in-memory)))
      (equal
       (nth
        11
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_numheads fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-14
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        12
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_hiddsec fat32-in-memory)))
      (equal
       (nth
        13
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bpb_hiddsec fat32-in-memory))))
      (equal
       (nth
        14
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_hiddsec fat32-in-memory))))
      (equal
       (nth
        15
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 24 (bpb_hiddsec fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-15
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        16
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_totsec32 fat32-in-memory)))
      (equal
       (nth
        17
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bpb_totsec32 fat32-in-memory))))
      (equal
       (nth
        18
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_totsec32 fat32-in-memory))))
      (equal
       (nth
        19
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 24 (bpb_totsec32 fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-16
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        20
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_fatsz32 fat32-in-memory)))
      (equal
       (nth
        21
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail 8 (bpb_fatsz32 fat32-in-memory))))
      (equal
       (nth
        22
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_fatsz32 fat32-in-memory))))
      (equal
       (nth
        23
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 24 (bpb_fatsz32 fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-17
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        24
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_extflags fat32-in-memory)))
      (equal
       (nth
        25
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_extflags fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-18
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth
       26
       (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
      (bpb_fsver_minor fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-19
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth
       27
       (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
      (bpb_fsver_major fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-20
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        28
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_rootclus fat32-in-memory)))
      (equal
       (nth
        29
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bpb_rootclus fat32-in-memory))))
      (equal
       (nth
        30
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bpb_rootclus fat32-in-memory))))
      (equal
       (nth
        31
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 24 (bpb_rootclus fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-21
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        32
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_fsinfo fat32-in-memory)))
      (equal
       (nth
        33
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_fsinfo fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-22
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        34
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bpb_bkbootsec fat32-in-memory)))
      (equal
       (nth
        35
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 8 (bpb_bkbootsec fat32-in-memory))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-23
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth
       48
       (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
      (bs_drvnum fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-24
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth
       49
       (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
      (bs_reserved1 fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-25
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (nth
       50
       (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
      (bs_bootsig fat32-in-memory))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-26
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (and
      (equal
       (nth
        51
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (bs_volid fat32-in-memory)))
      (equal
       (nth
        52
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail  8 (bs_volid fat32-in-memory))))
      (equal
       (nth
        53
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (loghead 8 (logtail 16 (bs_volid fat32-in-memory))))
      (equal
       (nth
        54
        (get-remaining-rsvdbyts (fat32-in-memory-to-string fat32-in-memory)))
       (logtail 24 (bs_volid fat32-in-memory)))))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-27
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (unsigned-byte-listp 8 (nth *data-regioni* fat32-in-memory)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (implies
              (fat32-in-memoryp fat32-in-memory)
              (true-listp (nth *data-regioni* fat32-in-memory))))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-28
  (implies
   (compliant-fat32-in-memoryp fat32-in-memory)
   (equal
    (nthcdr
     (* (bpb_bytspersec fat32-in-memory)
        (bpb_rsvdseccnt fat32-in-memory))
     (explode (fat32-in-memory-to-string fat32-in-memory)))
    (append
     (explode (make-fat-string-ac (bpb_numfats fat32-in-memory)
                                  fat32-in-memory ""))
     (nats=>chars (nth *data-regioni* fat32-in-memory)))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (fat32-in-memory-to-string nats=>chars-of-revappend
                                data-region-length
                                true-list-fix-when-true-listp)
     (reverse-removal)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (local
   (defthm fat32-in-memory-to-string-inversion-lemma-29
     (implies (and (not (zp j)) (integerp i) (> i j))
              (> (floor i j) 0))
     :rule-classes :linear))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-30
    (implies (and (fat32-in-memoryp fat32-in-memory)
                  (<= 512 (bpb_bytspersec fat32-in-memory))
                  (<= 1 (bpb_secperclus fat32-in-memory))
                  (> (+ (- (bpb_rsvdseccnt fat32-in-memory))
                        (bpb_totsec32 fat32-in-memory)
                        (- (* (bpb_fatsz32 fat32-in-memory)
                              (bpb_numfats fat32-in-memory))))
                     (bpb_secperclus fat32-in-memory)))
             (> (* (bpb_bytspersec fat32-in-memory)
                   (bpb_secperclus fat32-in-memory)
                   (floor (+ (- (bpb_rsvdseccnt fat32-in-memory))
                             (bpb_totsec32 fat32-in-memory)
                             (- (* (bpb_fatsz32 fat32-in-memory)
                                   (bpb_numfats fat32-in-memory))))
                          (bpb_secperclus fat32-in-memory)))
                0))
    :rule-classes :linear
    :instructions
    (:promote (:rewrite product-greater-than-zero-2)
              (:change-goal nil t)
              :bash :s-prop
              (:rewrite product-greater-than-zero-2)
              (:change-goal nil t)
              :bash :s-prop
              (:use (:instance fat32-in-memory-to-string-inversion-lemma-29
                               (i (+ (- (bpb_rsvdseccnt fat32-in-memory))
                                     (bpb_totsec32 fat32-in-memory)
                                     (- (* (bpb_fatsz32 fat32-in-memory)
                                           (bpb_numfats fat32-in-memory)))))
                               (j (bpb_secperclus fat32-in-memory))))
              :promote (:demote 1)
              (:dive 1 1)
              (:= t)
              :top :bash))

  (defthm fat32-in-memory-to-string-inversion-lemma-31
    (implies (compliant-fat32-in-memoryp fat32-in-memory)
             (<=
              (* 4 (fat-length fat32-in-memory))
              (* (bpb_numfats fat32-in-memory)
                 4 (fat-length fat32-in-memory))))
    :rule-classes :linear))

(defthm fat32-in-memory-to-string-inversion-lemma-32
  (implies (and (unsigned-byte-p 8 a3)
                (unsigned-byte-p 8 a2)
                (unsigned-byte-p 8 a1)
                (unsigned-byte-p 8 a0))
           (fat32-entry-p (combine32u a3 a2 a1 a0)))
  :hints (("goal" :in-theory (e/d (fat32-entry-p)
                                  (unsigned-byte-p)))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-33
  (implies (fat32-in-memoryp fat32-in-memory)
           (equal (resize-fat (fat-length fat32-in-memory)
                              fat32-in-memory)
                  fat32-in-memory))
  :hints (("goal" :in-theory (enable resize-fat fat-length))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-34
  (implies (fat32-in-memoryp fat32-in-memory)
           (equal (resize-data-region (data-region-length fat32-in-memory)
                                      fat32-in-memory)
                  fat32-in-memory))
  :hints (("goal" :in-theory (enable resize-data-region data-region-length)))
  :rule-classes (:rewrite
                 (:rewrite :corollary
                           (implies
                            (fat32-in-memoryp fat32-in-memory)
                            (equal (resize-data-region
                                    (len
                                     (nth *data-regioni* fat32-in-memory))
                                    fat32-in-memory)
                                   fat32-in-memory))
                           :hints (("Goal" :in-theory (enable resize-data-region))))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-36
  (implies
   (and (natp n2)
        (< n2 (* 4 (fat-length fat32-in-memory)))
        (not (zp n1)))
   (equal
    (nth n2
         (explode (make-fat-string-ac n1 fat32-in-memory ac)))
    (nth n2
         (explode (stobj-fa-table-to-string
                   fat32-in-memory
                   (fat-length fat32-in-memory))))))
  :hints (("Goal" :in-theory (enable make-fat-string-ac))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-37
  (implies
   (and (fat32-entry-p current)
        (< (nfix n) 4))
   (unsigned-byte-p 8
                    (nth n
                         (list (loghead 8 current)
                               (loghead 8 (logtail 8 current))
                               (loghead 8 (logtail 16 current))
                               (logtail 24 current)))))
  :hints
  (("goal" :in-theory (e/d (fat32-entry-p)
                           (unsigned-byte-p loghead logtail))))
  :rule-classes
  ((:linear
    :corollary
    (implies
     (and (fat32-entry-p current)
          (< (nfix n) 4))
     (and (<= 0
              (nth n
                   (list (loghead 8 current)
                         (loghead 8 (logtail 8 current))
                         (loghead 8 (logtail 16 current))
                         (logtail 24 current))))
          (< (nth n
                  (list (loghead 8 current)
                        (loghead 8 (logtail 8 current))
                        (loghead 8 (logtail 16 current))
                        (logtail 24 current)))
             256))))
   (:rewrite
    :corollary
    (implies
     (and (fat32-entry-p current)
          (< (nfix n) 4))
     (integerp (nth n
                    (list (loghead 8 current)
                          (loghead 8 (logtail 8 current))
                          (loghead 8 (logtail 16 current))
                          (logtail 24 current))))))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-38
  (implies (and (integerp pos)
                (integerp length)
                (<= pos length))
           (and (iff (< (+ -1 (* 4 pos)) (+ -4 (* 4 length)))
                     (not (equal pos length)))
                (iff (< (+ -2 (* 4 pos)) (+ -4 (* 4 length)))
                     (not (equal pos length)))
                (iff (< (+ -3 (* 4 pos)) (+ -4 (* 4 length)))
                     (not (equal pos length)))
                (iff (< (+ -4 (* 4 pos)) (+ -4 (* 4 length)))
                     (not (equal pos length))))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-39
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (not (zp pos))
        (integerp length)
        (<= pos length)
        (<= length (fat-length fat32-in-memory)))
   (and
    (equal
     (nth
      (+ -1 (* 4 pos))
      (explode
       (stobj-fa-table-to-string fat32-in-memory length)))
     (code-char (logtail 24 (fati (- pos 1) fat32-in-memory))))
    (equal
     (nth
      (+ -2 (* 4 pos))
      (explode
       (stobj-fa-table-to-string fat32-in-memory length)))
     (code-char
      (loghead 8
               (logtail 16 (fati (- pos 1) fat32-in-memory)))))
    (equal
     (nth
      (+ -3 (* 4 pos))
      (explode
       (stobj-fa-table-to-string fat32-in-memory length)))
     (code-char
      (loghead 8
               (logtail 8 (fati (- pos 1) fat32-in-memory)))))
    (equal
     (nth
      (+ -4 (* 4 pos))
      (explode
       (stobj-fa-table-to-string fat32-in-memory length)))
     (code-char (loghead 8 (fati (- pos 1) fat32-in-memory))))))
  :hints (("goal" :in-theory (e/d (stobj-fa-table-to-string) (logtail loghead)))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-40
  (implies (and (fat32-in-memoryp fat32-in-memory)
                (< (nfix i)
                   (fat-length fat32-in-memory)))
           (equal (update-fati i (fati i fat32-in-memory)
                               fat32-in-memory)
                  fat32-in-memory))
  :hints
  (("goal" :in-theory (enable fati update-fati fat-length))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-41
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (not (zp pos))
        (<= pos (fat-length fat32-in-memory)))
   (equal (update-fat
           fat32-in-memory
           (make-fat-string-ac (bpb_numfats fat32-in-memory)
                               fat32-in-memory "")
           pos)
          fat32-in-memory))
  :hints
  (("goal"
    :induct
    (update-fat
     fat32-in-memory
     (make-fat-string-ac (bpb_numfats fat32-in-memory)
                         fat32-in-memory "")
     pos)
    :in-theory (e/d (compliant-fat32-in-memoryp)
                    (loghead logtail fat32-in-memoryp)))))

(encapsulate
  ()

  (local (in-theory (disable bs_jmpbooti update-bs_jmpbooti
                             bs_oemnamei bpb_reservedi bs_vollabi
                             bs_filsystypei loghead logtail)))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-43
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (chars=>nats (explode (reserved-area-string fat32-in-memory)))
      (append
       ;; initial bytes
       (list (bs_jmpbooti 0 fat32-in-memory)
             (bs_jmpbooti 1 fat32-in-memory)
             (bs_jmpbooti 2 fat32-in-memory))
       (list (bs_oemnamei 0 fat32-in-memory)
             (bs_oemnamei 1 fat32-in-memory)
             (bs_oemnamei 2 fat32-in-memory)
             (bs_oemnamei 3 fat32-in-memory)
             (bs_oemnamei 4 fat32-in-memory)
             (bs_oemnamei 5 fat32-in-memory)
             (bs_oemnamei 6 fat32-in-memory)
             (bs_oemnamei 7 fat32-in-memory))
       (list (loghead 8 (bpb_bytspersec fat32-in-memory))
             (logtail 8 (bpb_bytspersec fat32-in-memory))
             (bpb_secperclus fat32-in-memory)
             (loghead 8 (bpb_rsvdseccnt fat32-in-memory))
             (logtail 8 (bpb_rsvdseccnt fat32-in-memory)))
       ;; remaining reserved bytes
       (list (bpb_numfats fat32-in-memory)
             (loghead 8 (bpb_rootentcnt fat32-in-memory))
             (logtail 8 (bpb_rootentcnt fat32-in-memory))
             (loghead 8 (bpb_totsec16 fat32-in-memory))
             (logtail 8 (bpb_totsec16 fat32-in-memory))
             (bpb_media fat32-in-memory)
             (loghead 8 (bpb_fatsz16 fat32-in-memory))
             (logtail 8 (bpb_fatsz16 fat32-in-memory))
             (loghead 8 (bpb_secpertrk fat32-in-memory))
             (logtail 8 (bpb_secpertrk fat32-in-memory))
             (loghead 8 (bpb_numheads fat32-in-memory))
             (logtail 8 (bpb_numheads fat32-in-memory))
             (loghead 8             (bpb_hiddsec fat32-in-memory) )
             (loghead 8 (logtail  8 (bpb_hiddsec fat32-in-memory)))
             (loghead 8 (logtail 16 (bpb_hiddsec fat32-in-memory)))
             (logtail 24 (bpb_hiddsec fat32-in-memory) )
             (loghead 8             (bpb_totsec32 fat32-in-memory) )
             (loghead 8 (logtail  8 (bpb_totsec32 fat32-in-memory)))
             (loghead 8 (logtail 16 (bpb_totsec32 fat32-in-memory)))
             (logtail 24 (bpb_totsec32 fat32-in-memory) )
             (loghead 8             (bpb_fatsz32 fat32-in-memory) )
             (loghead 8 (logtail  8 (bpb_fatsz32 fat32-in-memory)))
             (loghead 8 (logtail 16 (bpb_fatsz32 fat32-in-memory)))
             (logtail 24 (bpb_fatsz32 fat32-in-memory) )
             (loghead 8 (bpb_extflags fat32-in-memory))
             (logtail 8 (bpb_extflags fat32-in-memory))
             (bpb_fsver_minor fat32-in-memory)
             (bpb_fsver_major fat32-in-memory)
             (loghead 8             (bpb_rootclus fat32-in-memory) )
             (loghead 8 (logtail  8 (bpb_rootclus fat32-in-memory)))
             (loghead 8 (logtail 16 (bpb_rootclus fat32-in-memory)))
             (logtail 24 (bpb_rootclus fat32-in-memory) )
             (loghead 8 (bpb_fsinfo fat32-in-memory))
             (logtail 8 (bpb_fsinfo fat32-in-memory))
             (loghead 8 (bpb_bkbootsec fat32-in-memory))
             (logtail 8 (bpb_bkbootsec fat32-in-memory)))
       (list (bpb_reservedi  0 fat32-in-memory)
             (bpb_reservedi  1 fat32-in-memory)
             (bpb_reservedi  2 fat32-in-memory)
             (bpb_reservedi  3 fat32-in-memory)
             (bpb_reservedi  4 fat32-in-memory)
             (bpb_reservedi  5 fat32-in-memory)
             (bpb_reservedi  6 fat32-in-memory)
             (bpb_reservedi  7 fat32-in-memory)
             (bpb_reservedi  8 fat32-in-memory)
             (bpb_reservedi  9 fat32-in-memory)
             (bpb_reservedi 10 fat32-in-memory)
             (bpb_reservedi 11 fat32-in-memory))
       (list (bs_drvnum fat32-in-memory)
             (bs_reserved1 fat32-in-memory)
             (bs_bootsig fat32-in-memory)
             (loghead 8             (bs_volid fat32-in-memory) )
             (loghead 8 (logtail  8 (bs_volid fat32-in-memory)))
             (loghead 8 (logtail 16 (bs_volid fat32-in-memory)))
             (logtail 24 (bs_volid fat32-in-memory) ))
       (list (bs_vollabi  0 fat32-in-memory)
             (bs_vollabi  1 fat32-in-memory)
             (bs_vollabi  2 fat32-in-memory)
             (bs_vollabi  3 fat32-in-memory)
             (bs_vollabi  4 fat32-in-memory)
             (bs_vollabi  5 fat32-in-memory)
             (bs_vollabi  6 fat32-in-memory)
             (bs_vollabi  7 fat32-in-memory)
             (bs_vollabi  8 fat32-in-memory)
             (bs_vollabi  9 fat32-in-memory)
             (bs_vollabi 10 fat32-in-memory))
       (list (bs_filsystypei 0 fat32-in-memory)
             (bs_filsystypei 1 fat32-in-memory)
             (bs_filsystypei 2 fat32-in-memory)
             (bs_filsystypei 3 fat32-in-memory)
             (bs_filsystypei 4 fat32-in-memory)
             (bs_filsystypei 5 fat32-in-memory)
             (bs_filsystypei 6 fat32-in-memory)
             (bs_filsystypei 7 fat32-in-memory))
       (make-list
        (- (* (bpb_rsvdseccnt fat32-in-memory) (bpb_bytspersec fat32-in-memory)) 90)
        :initial-element 0)))) :hints (("Goal" :in-theory (e/d (chars=>nats
                                                                reserved-area-string
                                                                reserved-area-chars)
                                                               (loghead
                                                                logtail
                                                                unsigned-byte-p)))))

  (local (in-theory (enable chars=>nats-of-take)))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-44
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (update-bs_jmpboot
       (take 3
             (get-initial-bytes (fat32-in-memory-to-string fat32-in-memory)))
       fat32-in-memory)
      fat32-in-memory)) :hints (("Goal" :in-theory (e/d (get-initial-bytes
                                                         fat32-in-memory-to-string
                                                         compliant-fat32-in-memoryp)
                                                        (fat32-in-memoryp)))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-45
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (update-bs_oemname
       (take 8
             (nthcdr 3
                     (get-initial-bytes
                      (fat32-in-memory-to-string
                       fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory)) :hints (("Goal" :in-theory (e/d (get-initial-bytes
                                                         fat32-in-memory-to-string
                                                         compliant-fat32-in-memoryp)
                                                        (fat32-in-memoryp)))))

  (local (in-theory (enable chars=>nats-of-nthcdr)))

  (local
   (defthm
     fat32-in-memory-to-string-inversion-lemma-46
     (implies
      (compliant-fat32-in-memoryp fat32-in-memory)
      (not
       (<
        (if
            (<
             (binary-+
              '-16
              (binary-+
               (data-region-length fat32-in-memory)
               (binary-+
                (binary-* (bpb_bytspersec fat32-in-memory)
                          (bpb_rsvdseccnt fat32-in-memory))
                (binary-* (bpb_numfats fat32-in-memory)
                          (binary-* '4
                                    (fat-length fat32-in-memory))))))
             '0)
            '0
          (binary-+
           '-16
           (binary-+
            (data-region-length fat32-in-memory)
            (binary-+
             (binary-* (bpb_bytspersec fat32-in-memory)
                       (bpb_rsvdseccnt fat32-in-memory))
             (binary-* (bpb_numfats fat32-in-memory)
                       (binary-* '4
                                 (fat-length fat32-in-memory)))))))
        (binary-+ '-16
                  (binary-* (bpb_bytspersec fat32-in-memory)
                            (bpb_rsvdseccnt fat32-in-memory))))))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-47
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (update-bs_vollab
       (take 11
             (nthcdr 55
                     (get-remaining-rsvdbyts
                      (fat32-in-memory-to-string
                       fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory)) :hints (("Goal" :in-theory (e/d (get-initial-bytes
                                                         get-remaining-rsvdbyts
                                                         fat32-in-memory-to-string
                                                         compliant-fat32-in-memoryp)
                                                        (fat32-in-memoryp)))))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-48
    (implies
     (compliant-fat32-in-memoryp fat32-in-memory)
     (equal
      (update-bs_filsystype
       (take 8
             (nthcdr 66
                     (get-remaining-rsvdbyts
                      (fat32-in-memory-to-string
                       fat32-in-memory))))
       fat32-in-memory)
      fat32-in-memory)) :hints (("Goal" :in-theory (e/d (get-initial-bytes
                                                         get-remaining-rsvdbyts
                                                         fat32-in-memory-to-string
                                                         compliant-fat32-in-memoryp)
                                                        (fat32-in-memoryp))))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-51
  (implies
   (and (natp n2)
        (zp (+ n2
               (- (* 4 (fat-length fat32-in-memory)))))
        (not (zp n1)))
   (equal
    (take n2
          (explode (make-fat-string-ac n1 fat32-in-memory ac)))
    (take n2
          (explode (stobj-fa-table-to-string
                    fat32-in-memory
                    (fat-length fat32-in-memory))))))
  :hints
  (("goal" :in-theory (enable true-list-fix-when-true-listp make-fat-string-ac))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-52
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (not (zp pos))
        (<= pos (fat-length fat32-in-memory)))
   (equal (update-fat
           fat32-in-memory
           (stobj-fa-table-to-string fat32-in-memory
                                     (fat-length fat32-in-memory))
           pos)
          fat32-in-memory))
  :hints
  (("goal"
    :induct
    (update-fat
     fat32-in-memory
     (stobj-fa-table-to-string fat32-in-memory
                               (fat-length fat32-in-memory))
     pos)
    :in-theory (e/d (compliant-fat32-in-memoryp)
                    (loghead logtail fat32-in-memoryp)))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-53
  (implies
   (and (compliant-fat32-in-memoryp fat32-in-memory)
        (integerp n)
        (<= (+ (* (bpb_rsvdseccnt fat32-in-memory)
                  (bpb_bytspersec fat32-in-memory))
               (* (nfix (bpb_numfats fat32-in-memory))
                  (fat-length fat32-in-memory)
                  4))
            n))
   (equal
    (nthcdr
     n
     (explode (fat32-in-memory-to-string fat32-in-memory)))
    (nthcdr
     (+ n
        (- (* (bpb_bytspersec fat32-in-memory)
              (bpb_rsvdseccnt fat32-in-memory)))
        (- (* (bpb_numfats fat32-in-memory)
              4 (fat-length fat32-in-memory))))
     (nats=>chars (nth *data-regioni* fat32-in-memory)))))
  :hints
  (("goal" :in-theory (enable fat32-in-memory-to-string
                              nats=>chars-of-revappend
                              data-region-length
                              true-list-fix-when-true-listp))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    fat32-in-memory-to-string-inversion-lemma-54
    (implies
     (equal (* (bpb_fatsz32 fat32-in-memory)
               1/4 (bpb_bytspersec fat32-in-memory))
            (fat-length fat32-in-memory))
     (equal (* (bpb_bytspersec fat32-in-memory)
               (bpb_fatsz32 fat32-in-memory)
               (bpb_numfats fat32-in-memory))
            (* (bpb_numfats fat32-in-memory)
               4 (fat-length fat32-in-memory))))))

(defthm
  fat32-in-memory-to-string-inversion-lemma-55
  (implies
   (fat32-in-memoryp fat32-in-memory)
   (equal (update-nth *data-regioni*
                      (nth *data-regioni* fat32-in-memory)
                      fat32-in-memory)
          fat32-in-memory)))

(encapsulate
  ()

  (local (in-theory (e/d (nthcdr-when->=-n-len-l true-list-fix-when-true-listp
                                                 chars=>nats-of-revappend
                                                 nats=>chars-of-revappend
                                                 update-data-region-correctness-1
                                                 data-region-length
                                                 ;; both of the following
                                                 ;; rules, i would like to disable
                                                 cluster-size count-of-clusters)
                         (fat32-in-memoryp loghead logtail nth
                                           floor))))

  (defthm
    fat32-in-memory-to-string-inversion
    (implies
     (and
      (compliant-fat32-in-memoryp fat32-in-memory)
      (integerp (* (bpb_fatsz32 fat32-in-memory)
                   1/4 (bpb_bytspersec fat32-in-memory)))
      (> (+ (- (bpb_rsvdseccnt fat32-in-memory))
            (bpb_totsec32 fat32-in-memory)
            (- (* (bpb_fatsz32 fat32-in-memory)
                  (bpb_numfats fat32-in-memory))))
         (bpb_secperclus fat32-in-memory))
      (>= 140737482588160
          (* (bpb_bytspersec fat32-in-memory)
             (bpb_secperclus fat32-in-memory)
             (floor (+ (- (bpb_rsvdseccnt fat32-in-memory))
                       (bpb_totsec32 fat32-in-memory)
                       (- (* (bpb_fatsz32 fat32-in-memory)
                             (bpb_numfats fat32-in-memory))))
                    (bpb_secperclus fat32-in-memory))))
      (equal
       (* (bpb_fatsz32 fat32-in-memory)
          1/4 (bpb_bytspersec fat32-in-memory))
       (fat-length fat32-in-memory))
      (equal
       (*
        (bpb_bytspersec fat32-in-memory)
        (bpb_secperclus fat32-in-memory)
        (floor
         (+
          (- (bpb_rsvdseccnt fat32-in-memory))
          (bpb_totsec32 fat32-in-memory)
          (- (* (bpb_fatsz32 fat32-in-memory)
                (bpb_numfats fat32-in-memory))))
         (bpb_secperclus fat32-in-memory)))
       (data-region-length fat32-in-memory)))
     (equal
      (mv-nth 0
              (string-to-fat32-in-memory
               fat32-in-memory
               (fat32-in-memory-to-string
                fat32-in-memory)))
      fat32-in-memory))))

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
