(in-package "ACL2")

(include-book "utilities/flatten-equiv")
(include-book "hifat-to-lofat-inversion")
(include-book "lofat-to-string-inversion")
(local (include-book "std/lists/prefixp" :dir :system))
(local (include-book "std/lists/intersectp" :dir :system))

;  eqfat.lisp                                           Mihir Mehta

; This is an equivalence relation between instances of LoFAT.

;; get-cc-alt really should be disabled here if it can!
(local
 (in-theory (e/d ((:rewrite hifat-equiv-of-cons-lemma-4)
                  (:rewrite not-intersectp-list-of-cons-2))
                 ((:rewrite free-index-list-listp-of-update-nth-lemma-1)
                  (:rewrite free-index-list-listp-correctness-1)
                  (:rewrite non-free-index-list-listp-correctness-1)
                  (:rewrite count-free-clusters-of-set-indices-in-fa-table-2)
                  (:rewrite count-free-clusters-of-set-indices-in-fa-table-lemma-1)
                  (:rewrite non-free-index-listp-correctness-5)
                  (:rewrite free-index-listp-correctness-1)
                  (:rewrite consp-of-assoc-of-hifat-file-alist-fix)
                  (:linear hifat-entry-count-when-hifat-subsetp)
                  (:rewrite consp-of-assoc-when-hifat-equiv-lemma-1)
                  (:rewrite hifat-subsetp-preserves-assoc)
                  (:rewrite abs-find-file-correctness-1-lemma-40)
                  (:rewrite hifat-file-alist-fix-guard-lemma-1)
                  (:rewrite natp-of-caar-when-fd-table-p)
                  (:rewrite natp-of-caar-when-file-table-p)
                  (:rewrite fat32-filename-p-of-car-when-fat32-filename-list-p)
                  (:rewrite d-e-list-p-of-cdr-when-d-e-list-p)
                  (:rewrite fat32-masked-entry-list-p-when-bounded-nat-listp)
                  (:linear find-n-free-clusters-correctness-1)
                  (:rewrite fat32-masked-entry-list-p-when-not-consp)
                  (:rewrite bounded-nat-listp-correctness-1)
                  (:rewrite stringp-when-nonempty-stringp)
                  (:rewrite str::hex-digit-char-listp-of-cons)
                  (:definition logtail$inline)
                  (:definition loghead$inline)
                  (:rewrite nat-listp-when-unsigned-byte-listp)
                  (:rewrite take-of-too-many)
                  (:rewrite make-list-ac-removal)
                  (:rewrite true-list-listp-when-not-consp)
                  (:rewrite true-list-listp-of-cdr-when-true-list-listp)
                  (:rewrite rationalp-of-car-when-rational-listp)
                  (:rewrite integerp-of-car-when-integer-listp)
                  (:rewrite acl2-numberp-of-car-when-acl2-number-listp)
                  (:rewrite subsetp-implies-subsetp-cdr)
                  (:rewrite revappend-removal)
                  (:rewrite not-intersectp-list-of-set-difference$-lemma-2
                            . 1)
                  (:rewrite member-intersectp-is-commutative-lemma-2)
                  (:rewrite intersectp-member-when-not-member-intersectp)
                  (:rewrite not-intersectp-list-when-subsetp-2)
                  (:rewrite no-duplicatesp-of-member)
                  (:rewrite then-subseq-same-2)
                  (:rewrite subseq-of-length-1)
                  (:rewrite nth-when->=-n-len-l)
                  (:rewrite car-of-nthcdr)
                  (:rewrite assoc-of-car-when-member)
                  (:rewrite true-listp-when-string-list)
                  (:rewrite intersect-with-subset . 10)
                  (:rewrite intersect-with-subset . 8)
                  (:rewrite intersect-with-subset . 7)
                  (:rewrite intersect-with-subset . 4)
                  (:rewrite intersect-with-subset . 3)
                  (:rewrite intersect-with-subset . 2)
                  (:rewrite intersect-with-subset . 1)
                  (:rewrite subsetp-member . 4)
                  (:rewrite subsetp-member . 2)
                  (:rewrite consp-of-nthcdr)
                  (:induction integer-listp)
                  (:definition integer-listp)
                  (:definition rational-listp)
                  (:definition acl2-number-listp)
                  (:induction update-nth)
                  (:definition update-nth)
                  (:definition mod)
                  (:definition ceiling)
                  (:rewrite characterp-nth)
                  (:definition string-listp)
                  (:induction take)
                  (:definition take)
                  (:induction member-equal)
                  (:definition member-equal)
                  (:definition floor)
                  (:induction nth)
                  (:definition nth)
                  (:induction true-listp)
                  (:definition true-listp)
                  (:rewrite
                   member-intersectp-of-set-difference$-lemma-1)))))

;; I'm thinking it would be useful to eliminate a lot of case splits that arise
;; from nfix terms in lemmas using lofat-to-hifat-helper-correctness-4.
(local (in-theory (disable nfix)))

(defund-nx
  eqfat (str1 str2)
  (b*
      (((mv fat32$c1 error-code1)
        (string-to-lofat-nx str1))
       (good1 (and (stringp str1) (equal error-code1 0)))
       ((mv fat32$c2 error-code2)
        (string-to-lofat-nx str2))
       (good2 (and (stringp str2) (equal error-code2 0)))
       ((unless (and good1 good2))
        (and (not good1) (not good2))))
    (lofat-equiv fat32$c1 fat32$c2)))

(defequiv
  eqfat
  :hints (("goal" :in-theory (enable eqfat))))

(defthm
  string-to-lofat-inversion
  (implies
   (and (stringp str)
        (fat32$c-p fat32$c)
        (equal (mv-nth 1 (string-to-lofat fat32$c str))
               0))
   (eqfat (lofat-to-string
           (mv-nth 0
                   (string-to-lofat fat32$c str)))
          str))
  :hints
  (("goal"
    :in-theory (e/d (eqfat)
                    (create-fat32$c
                     (:rewrite lofat-to-string-inversion)))
    :use
    ((:instance
      (:rewrite lofat-to-string-inversion)
      (fat32$c
       (mv-nth 0
               (string-to-lofat (create-fat32$c)
                                str))))
     (:instance
      (:rewrite string-to-lofat-ignore-lemma-14)
      (str
       (lofat-to-string
        (mv-nth 0
                (string-to-lofat (create-fat32$c)
                                 str))))
      (fat32$c
       (mv-nth 0
               (string-to-lofat (create-fat32$c)
                                str))))
     string-to-lofat-ignore-lemma-14))))

(defthm
  hifat-to-string-inversion
  (implies
   (and (lofat-fs-p fat32$c)
        (m1-file-alist-p fs)
        (hifat-bounded-file-alist-p fs)
        (hifat-no-dups-p fs)
        (<= (hifat-entry-count fs)
            (max-entry-count fat32$c)))
   (b*
       (((mv fat32$c error-code)
         (hifat-to-lofat fat32$c fs)))
     (implies
      (zp error-code)
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat
         (mv-nth
          0
          (string-to-lofat
           fat32$c
           (lofat-to-string fat32$c)))))
       fs)))))

(defthm
  string-to-hifat-inversion
  (implies
   (and (stringp str)
        (fat32$c-p fat32$c))
   (b*
       (((mv fat32$c error-code1)
         (string-to-lofat fat32$c str))
        ((mv fs error-code2)
         (lofat-to-hifat fat32$c)))
     (implies
      (and (equal error-code1 0)
           (equal error-code2 0)
           (hifat-bounded-file-alist-p fs)
           (hifat-no-dups-p fs)
           (equal (mv-nth 1 (hifat-to-lofat fat32$c fs))
                  0))
      (eqfat (lofat-to-string
              (mv-nth 0 (hifat-to-lofat fat32$c fs)))
             str))))
  :hints
  (("goal"
    :in-theory (e/d (eqfat)
                    ((:rewrite lofat-to-string-inversion)
                     (:rewrite string-to-lofat-ignore)))
    :use
    ((:instance
      (:rewrite lofat-to-string-inversion)
      (fat32$c
       (mv-nth
        0
        (hifat-to-lofat
         (mv-nth 0 (string-to-lofat-nx str))
         (mv-nth 0
                 (lofat-to-hifat
                  (mv-nth 0 (string-to-lofat-nx str))))))))
     (:instance
      (:rewrite string-to-lofat-ignore)
      (str
       (lofat-to-string
        (mv-nth
         0
         (hifat-to-lofat
          (mv-nth 0 (string-to-lofat-nx str))
          (mv-nth 0
                  (lofat-to-hifat
                   (mv-nth 0 (string-to-lofat-nx str))))))))
      (fat32$c
       (mv-nth
        0
        (hifat-to-lofat
         (mv-nth 0 (string-to-lofat-nx str))
         (mv-nth 0
                 (lofat-to-hifat
                  (mv-nth 0 (string-to-lofat-nx str))))))))
     (:rewrite string-to-lofat-ignore)
     string-to-lofat-ignore-lemma-14
     (:instance
      (:rewrite string-to-lofat-ignore-lemma-14)
      (str
       (lofat-to-string
        (mv-nth
         0
         (hifat-to-lofat
          (mv-nth 0 (string-to-lofat fat32$c str))
          (mv-nth
           0
           (lofat-to-hifat
            (mv-nth 0
                    (string-to-lofat fat32$c str))))))))
      (fat32$c
       (mv-nth
        0
        (hifat-to-lofat
         (mv-nth 0 (string-to-lofat fat32$c str))
         (mv-nth
          0
          (lofat-to-hifat
           (mv-nth 0
                   (string-to-lofat fat32$c str))))))))
     (:instance
      (:rewrite lofat-to-string-inversion)
      (fat32$c
       (mv-nth
        0
        (hifat-to-lofat
         (mv-nth 0 (string-to-lofat fat32$c str))
         (mv-nth
          0
          (lofat-to-hifat
           (mv-nth
            0
            (string-to-lofat fat32$c str))))))))))))

#|
Some (rather awful) testing forms are
(b* (((mv contents &)
(get-cc-contents fat32$c 2 *ms-max-dir-size*)))
(get-dir-filenames fat32$c contents *ms-max-dir-size*))
(b* (((mv dir-contents &)
(get-cc-contents fat32$c 2 *ms-max-dir-size*)))
(lofat-to-hifat fat32$c))
(b* (((mv dir-contents &)
(get-cc-contents fat32$c 2 *ms-max-dir-size*))
(fs (lofat-to-hifat fat32$c)))
(hifat-open (list "INITRD  IMG") nil nil))
(b* (((mv dir-contents &)
(get-cc-contents fat32$c 2 *ms-max-dir-size*))
(fs (lofat-to-hifat fat32$c))
((mv fd-table file-table & &)
(hifat-open (list "INITRD  IMG") nil nil)))
(hifat-pread 0 6 49 fs fd-table file-table))
(b* (((mv dir-contents &)
(get-cc-contents fat32$c 2 *ms-max-dir-size*))
(fs (lofat-to-hifat fat32$c))
((mv fd-table file-table & &)
(hifat-open (list "INITRD  IMG") nil nil)))
(hifat-pwrite 0 "ornery" 49 fs fd-table file-table))
(b* (((mv dir-contents &)
(get-cc-contents fat32$c 2 *ms-max-dir-size*))
(fs (lofat-to-hifat fat32$c))
((mv fd-table file-table & &)
(hifat-open (list "INITRD  IMG") nil nil))
((mv fs & &)
(hifat-pwrite 0 "ornery" 49 fs fd-table file-table))
((mv fat32$c d-e-list)
(hifat-to-lofat-helper fat32$c fs)))
(mv fat32$c d-e-list))
(b* (((mv dir-contents &)
(get-cc-contents fat32$c 2 *ms-max-dir-size*))
(fs (lofat-to-hifat fat32$c))
((mv fd-table file-table & &)
(hifat-open (list "INITRD  IMG") nil nil))
((mv fs & &)
(hifat-pwrite 0 "ornery" 49 fs fd-table file-table)))
(hifat-to-lofat fat32$c fs))
(time$
(b*
((str (lofat-to-string
fat32$c))
((unless (and (stringp str)
(>= (length str) *initialbytcnt*)))
(mv fat32$c -1))
((mv fat32$c error-code)
(read-reserved-area fat32$c str))
((unless (equal error-code 0))
(mv fat32$c "it was read-reserved-area"))
(fat-read-size (/ (* (bpb_fatsz32 fat32$c)
(bpb_bytspersec fat32$c))
4))
((unless (integerp fat-read-size))
(mv fat32$c "it was fat-read-size"))
(data-byte-count (* (count-of-clusters fat32$c)
(cluster-size fat32$c)))
((unless (> data-byte-count 0))
(mv fat32$c "it was data-byte-count"))
(tmp_bytspersec (bpb_bytspersec fat32$c))
(tmp_init (* tmp_bytspersec
(+ (bpb_rsvdseccnt fat32$c)
(* (bpb_numfats fat32$c)
(bpb_fatsz32 fat32$c)))))
((unless (>= (length str)
(+ tmp_init
(data-region-length fat32$c))))
(mv fat32$c "it was (length str)"))
(fat32$c (resize-fat fat-read-size fat32$c))
(fat32$c
(update-fat fat32$c
(subseq str
(* (bpb_rsvdseccnt fat32$c)
(bpb_bytspersec fat32$c))
(+ (* (bpb_rsvdseccnt fat32$c)
(bpb_bytspersec fat32$c))
(* fat-read-size 4)))
fat-read-size))
(fat32$c
(resize-data-region data-byte-count fat32$c))
(data-region-string
(subseq str tmp_init
(+ tmp_init
(data-region-length fat32$c))))
(fat32$c
(update-data-region fat32$c data-region-string
(data-region-length fat32$c)
0)))
(mv fat32$c error-code)))
(time$
(b*
(((mv channel state)
(open-output-channel "test/disk2.raw" :character state))
(state
(princ$
(lofat-to-string fat32$c)
channel state))
(state
(close-output-channel channel state)))
(mv fat32$c state)))
(b* (((mv dir-contents &)
(get-cc-contents fat32$c 2 *ms-max-dir-size*))
(fs (lofat-to-hifat fat32$c))
((mv fs & &)
(hifat-mkdir fs (list "" "TMP        "))))
(hifat-to-lofat fat32$c fs))
|#

(defund lofat-file-contents-p (contents)
  (declare (xargs :guard t))
  (or (and (stringp contents)
           (unsigned-byte-p 32 (length contents)))
      (d-e-list-p contents)))

(defund lofat-file-contents-fix (contents)
  (declare (xargs :guard t))
  (if (lofat-file-contents-p contents)
      contents
    ""))

(defthm
  lofat-file-contents-fix-of-lofat-file-contents-fix
  (equal (lofat-file-contents-fix (lofat-file-contents-fix x))
         (lofat-file-contents-fix x))
  :hints (("goal" :in-theory (enable lofat-file-contents-fix))))

(fty::deffixtype lofat-file-contents
                 :pred lofat-file-contents-p
                 :fix lofat-file-contents-fix
                 :equiv lofat-file-contents-equiv
                 :define t)

(defthm
  lofat-file-contents-p-of-lofat-file-contents-fix
  (lofat-file-contents-p (lofat-file-contents-fix x))
  :hints (("goal" :in-theory (enable lofat-file-contents-fix
                                     lofat-file-contents-p))))

(defthm
  lofat-file-contents-fix-when-lofat-file-contents-p
  (implies (lofat-file-contents-p x)
           (equal (lofat-file-contents-fix x) x))
  :hints (("goal" :in-theory (enable lofat-file-contents-fix
                                     lofat-file-contents-p))))

(defthm
  lofat-file-contents-p-when-stringp
  (implies (stringp contents)
           (equal (lofat-file-contents-p contents)
                  (unsigned-byte-p 32 (length contents))))
  :hints (("goal" :in-theory (enable lofat-file-contents-p))))

(defthm lofat-file-contents-p-when-d-e-listp
  (implies (d-e-list-p contents)
           (lofat-file-contents-p contents))
  :hints (("goal" :in-theory (enable lofat-file-contents-p))))

(fty::defprod
 lofat-file
 ((d-e d-e-p :default (d-e-fix nil))
  (contents lofat-file-contents-p :default (lofat-file-contents-fix nil))))

(defund lofat-regular-file-p (file)
  (declare (xargs :guard t))
  (and (lofat-file-p file)
       (stringp (lofat-file->contents file))
       (unsigned-byte-p 32 (length (lofat-file->contents file)))))

(defund lofat-directory-file-p (file)
  (declare (xargs :guard t))
  (and (lofat-file-p file)
       (d-e-list-p (lofat-file->contents file))))

(defthm
  lofat-regular-file-p-correctness-1
  (implies
   (d-e-list-p contents)
   (not (lofat-regular-file-p (lofat-file d-e contents))))
  :hints (("goal" :in-theory (enable lofat-regular-file-p))))

(defthm
  lofat-regular-file-p-correctness-2
  (implies
   (lofat-regular-file-p file)
   (stringp (lofat-file->contents file)))
  :hints (("goal" :in-theory (enable lofat-regular-file-p))))

(defthm
  lofat-directory-file-p-correctness-1
  (implies
   (stringp contents)
   (not (lofat-directory-file-p (lofat-file d-e contents))))
  :hints (("goal" :in-theory (enable lofat-directory-file-p))))

(defthm
  lofat-directory-file-p-correctness-2
  (implies (lofat-regular-file-p file)
           (not (lofat-directory-file-p file)))
  :hints (("goal" :in-theory (enable lofat-directory-file-p
                                     lofat-regular-file-p))))

(defthm
  lofat-directory-file-p-when-lofat-file-p
  (implies (and (lofat-file-p file)
                (not (lofat-regular-file-p file)))
           (lofat-directory-file-p file))
  :hints (("goal" :in-theory (enable lofat-directory-file-p
                                     lofat-regular-file-p lofat-file-p
                                     lofat-file-contents-p
                                     lofat-file->contents))))

(defthm lofat-file-p-when-lofat-directory-file-p-or-lofat-regular-file-p
  (implies (or (lofat-directory-file-p file)
               (lofat-regular-file-p file))
           (lofat-file-p file))
  :hints (("goal" :in-theory (enable lofat-directory-file-p
                                     lofat-regular-file-p))))

(defthm lofat-file->d-e-under-true-equiv (true-equiv (lofat-file->d-e x) t))

(defun lofat-find-file (fat32$c d-e-list path)
  (declare (xargs :guard (and (lofat-fs-p fat32$c)
                              (fat32-filename-list-p path)
                              (useful-d-e-list-p d-e-list))
                  :measure (acl2-count path)
                  :stobjs fat32$c))
  (b* (((unless (consp path))
        (mv (make-lofat-file) *enoent*))
       (name (fat32-filename-fix (car path)))
       ((mv d-e error-code) (find-d-e d-e-list name))
       ((unless (equal error-code 0))
        (mv (make-lofat-file) error-code))
       (first-cluster (d-e-first-cluster d-e))
       (directory-p
        (d-e-directory-p d-e))
       ((mv contents &)
        (if
            (or (< first-cluster
                   *ms-first-data-cluster*)
                (>=
                 first-cluster
                 (+ (count-of-clusters fat32$c)
                    *ms-first-data-cluster*)))
            (mv "" 0)
          (d-e-cc-contents
           fat32$c d-e)))
       ((unless directory-p)
        (if (consp (cdr path))
            (mv (make-lofat-file) *enotdir*)
          (mv (make-lofat-file :d-e d-e :contents contents) 0)))
       ((when (atom (cdr path)))
        (mv
         (make-lofat-file :d-e d-e
                          :contents (make-d-e-list contents))
         0)))
    (lofat-find-file
     fat32$c (make-d-e-list contents) (cdr path))))

(defthm
  lofat-find-file-correctness-4
  (implies
   (lofat-directory-file-p (mv-nth 0
                                   (lofat-find-file fat32$c d-e-list path)))
   (d-e-list-p
    (lofat-file->contents (mv-nth 0
                                  (lofat-find-file fat32$c d-e-list path)))))
  :hints (("goal" :in-theory (enable lofat-find-file))))

(defthm
  lofat-find-file-correctness-lemma-1
  (implies
   (and (equal (mv-nth 1 (find-d-e d-e-list name))
               0)
        (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0)
        (or (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
               2)
            (<= (+ 2 (count-of-clusters fat32$c))
                (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name))))))
   (equal (assoc-equal
           name
           (mv-nth 0
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
          (cons name
                (make-m1-file :contents ""
                              :d-e (mv-nth 0 (find-d-e d-e-list name))))))
  :hints (("goal" :in-theory (e/d (lofat-to-hifat-helper)
                                  (nth-of-effective-fat)))))

(defthm
  lofat-find-file-correctness-lemma-2
  (implies
   (and (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0)
        (not (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name))))
        (<= 2
            (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name))))
        (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
           (+ 2 (count-of-clusters fat32$c))))
   (equal
    (assoc-equal
     name
     (mv-nth 0
             (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
    (cons
     name
     (make-m1-file
      :contents (mv-nth 0
                        (d-e-cc-contents fat32$c
                                         (mv-nth 0 (find-d-e d-e-list name))))
      :d-e (mv-nth 0 (find-d-e d-e-list name))))))
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper))))

(defthm
  lofat-find-file-correctness-lemma-3
  (implies
   (and (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0))
   (equal
    (m1-directory-file-p
     (cdr
      (assoc-equal
       name
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))))
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))))
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper
                                     m1-directory-file-p))))

;; Also general.
(defthm
  lofat-find-file-correctness-1-lemma-6
  (implies
   (and (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
        (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0))
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents
                 fat32$c
                 (mv-nth 0 (find-d-e d-e-list name)))))
       entry-limit))
     0)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents
                  fat32$c
                  (mv-nth 0 (find-d-e d-e-list name)))))
        entry-limit)))
     entry-limit)))
  :hints
  (("goal"
    :induct (mv (mv-nth 3
                        (lofat-to-hifat-helper fat32$c
                                               d-e-list entry-limit))
                (mv-nth 0 (find-d-e d-e-list name)))
    :in-theory
    (e/d (lofat-to-hifat-helper-correctness-4 lofat-to-hifat-helper)
         ((:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
          (:definition free-index-listp)
          (:rewrite nth-of-effective-fat)
          (:definition no-duplicatesp-equal)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
          (useful-d-e-list-p d-e-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32$c
                                                d-e-list entry-limit))
                 0))
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents
                  fat32$c
                  (mv-nth 0 (find-d-e d-e-list name)))))
        entry-limit))
      0)))
   (:linear
    :corollary
    (implies
     (and (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
          (useful-d-e-list-p d-e-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32$c
                                                d-e-list entry-limit))
                 0))
     (<
      (hifat-entry-count
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents
                   fat32$c
                   (mv-nth 0 (find-d-e d-e-list name)))))
         entry-limit)))
      entry-limit)))
   (:forward-chaining
    :corollary
    (implies
     (and (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
          (useful-d-e-list-p d-e-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32$c
                                                d-e-list entry-limit))
                 0))
     (equal
      (mv-nth
       3
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents
                  fat32$c
                  (mv-nth 0 (find-d-e d-e-list name)))))
        entry-limit))
      0))
    :trigger-terms
    ((lofat-to-hifat-helper
      fat32$c
      (make-d-e-list
       (mv-nth 0
               (d-e-cc-contents
                fat32$c
                (mv-nth 0 (find-d-e d-e-list name)))))
      entry-limit)))))

(defthm
  lofat-find-file-correctness-1-lemma-7
  (implies
   (and (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
        (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0))
   (equal
    (cdr (assoc-equal
          name
          (mv-nth 0
                  (lofat-to-hifat-helper fat32$c
                                         d-e-list entry-limit))))
    (make-m1-file
     :d-e (mv-nth 0 (find-d-e d-e-list name))
     :contents
     (mv-nth
      0
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          fat32$c
          (mv-nth 0 (find-d-e d-e-list name)))))
       entry-limit)))))
  :hints
  (("goal" :in-theory (enable lofat-to-hifat-helper-correctness-4)
    :induct (find-d-e d-e-list name)
    :expand (lofat-to-hifat-helper fat32$c
                                   d-e-list entry-limit))))

(defthm
  lofat-find-file-correctness-1-lemma-8
  (implies
   (and (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
        (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0))
   (and
    (<= 2
        (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name))))
    (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
       (+ 2
          (count-of-clusters fat32$c)))))
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper-correctness-4)
           :induct (find-d-e d-e-list name)
           :expand ((lofat-to-hifat-helper fat32$c
                                           d-e-list entry-limit)
                    (lofat-to-hifat-helper fat32$c
                                           nil (+ -1 entry-limit)))))
  :rule-classes :linear)

(defthm
  lofat-find-file-correctness-1
  (b*
      (((mv file error-code)
        (hifat-find-file
         (mv-nth 0
                 (lofat-to-hifat-helper
                  fat32$c
                  d-e-list entry-limit))
         path)))
    (implies
     (and
      (lofat-fs-p fat32$c)
      (useful-d-e-list-p d-e-list)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper
                      fat32$c
                      d-e-list entry-limit))
             0)
      (lofat-regular-file-p
       (mv-nth
        0
        (lofat-find-file fat32$c
                         d-e-list path))))
     (equal (lofat-find-file
             fat32$c d-e-list path)
            (mv (make-lofat-file :contents (m1-file->contents file)
                                 :d-e (m1-file->d-e file))
                error-code))))
  :hints (("Goal" :in-theory (enable hifat-find-file)) ))

(defthm
  lofat-find-file-correctness-2
  (b*
      (((mv file &)
        (hifat-find-file
         (mv-nth 0
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
         path)))
    (implies
     (and (lofat-fs-p fat32$c)
          (useful-d-e-list-p d-e-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
                 0)
          (lofat-directory-file-p
           (mv-nth 0
                   (lofat-find-file fat32$c d-e-list path))))
     (and
      (equal (lofat-file->d-e (mv-nth 0
                                      (lofat-find-file fat32$c d-e-list path)))
             (m1-file->d-e file))
      (equal
       (mv-nth 0
               (lofat-to-hifat-helper
                fat32$c
                (lofat-file->contents
                 (mv-nth 0
                         (lofat-find-file fat32$c d-e-list path)))
                entry-limit))
       (m1-file->contents file))
      (equal
       (mv-nth 3
               (lofat-to-hifat-helper
                fat32$c
                (lofat-file->contents
                 (mv-nth 0
                         (lofat-find-file fat32$c d-e-list path)))
                entry-limit))
       0))))
  :hints
  (("goal"
    :in-theory (enable hifat-find-file)
    :induct
    (mv
     (mv-nth
      0
      (hifat-find-file
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
       path))
     (mv-nth 0
             (lofat-find-file fat32$c d-e-list path)))
    :do-not-induct t
    :expand (lofat-to-hifat-helper fat32$c nil entry-limit))))

;; Replaces one of the corollaries of lofat-find-file-correctness-2.
(defthm
  lofat-find-file-correctness-5
  (implies
   (and (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0))
   (equal
    (mv-nth 1
            (lofat-find-file fat32$c d-e-list path))
    (mv-nth 1
            (hifat-find-file
             (mv-nth 0
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
             path))))
  :hints
  (("goal"
    :in-theory (enable hifat-find-file)
    :induct
    (mv
     (mv-nth
      0
      (hifat-find-file
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
       path))
     (mv-nth 0
             (lofat-find-file fat32$c d-e-list path)))
    :expand (lofat-to-hifat-helper fat32$c nil entry-limit))))

(defthm
  lofat-find-file-correctness-3
  (and (lofat-file-p
        (mv-nth 0
                (lofat-find-file fat32$c d-e-list path)))
       (natp (mv-nth 1
                     (lofat-find-file fat32$c
                                      d-e-list path))))
  :rule-classes
  ((:type-prescription
    :corollary (natp (mv-nth 1
                             (lofat-find-file fat32$c
                                              d-e-list path))))
   (:rewrite
    :corollary
    (lofat-file-p (mv-nth 0
                          (lofat-find-file fat32$c
                                           d-e-list path))))))

(defun
    place-d-e (d-e-list d-e)
  (declare (xargs :guard (and (d-e-p d-e)
                              (d-e-list-p d-e-list))))
  (b*
      ((d-e (mbe :exec d-e
                 :logic (d-e-fix d-e)))
       ((when (atom d-e-list))
        (list d-e))
       ((when (equal (d-e-filename d-e)
                     (d-e-filename (car d-e-list))))
        (list*
         d-e
         (mbe :exec (cdr d-e-list)
              :logic (d-e-list-fix (cdr d-e-list))))))
    (list* (mbe :logic (d-e-fix (car d-e-list))
                :exec (car d-e-list))
           (place-d-e (cdr d-e-list)
                      d-e))))

(defthm d-e-list-p-of-place-d-e
  (d-e-list-p (place-d-e d-e-list d-e)))

(defthm find-d-e-of-place-d-e
  (implies (d-e-list-p d-e-list)
           (equal (find-d-e (place-d-e d-e-list d-e)
                            filename)
                  (if (equal (d-e-filename d-e)
                             filename)
                      (mv (d-e-fix d-e) 0)
                    (find-d-e d-e-list filename)))))

(defthm
  place-d-e-of-d-e-fix
  (equal (place-d-e d-e-list (d-e-fix d-e))
         (place-d-e d-e-list d-e))
  :hints (("goal" :in-theory (enable place-d-e))))

(defcong d-e-equiv equal
  (place-d-e d-e-list d-e)
  2)

(defthm
  len-of-place-d-e
  (equal
   (len (place-d-e d-e-list d-e))
   (if (zp (mv-nth 1
                   (find-d-e d-e-list
                             (d-e-filename d-e))))
       (len d-e-list)
     (+ 1 (len d-e-list)))))

(defthm
  useful-d-e-list-p-of-place-d-e
  (implies
   (and (useful-d-e-list-p d-e-list)
        (not (useless-d-e-p (d-e-fix d-e)))
        (fat32-filename-p (d-e-filename d-e)))
   (useful-d-e-list-p (place-d-e d-e-list d-e)))
  :hints (("goal" :in-theory (enable useful-d-e-list-p
                                     fat32-filename-p))))

(defund clear-cc
  (fat32$c masked-current-cluster length)
  (declare
   (xargs :stobjs fat32$c
          :guard (and (lofat-fs-p fat32$c)
                      (fat32-masked-entry-p masked-current-cluster)
                      (natp length)
                      (>= masked-current-cluster
                          *ms-first-data-cluster*)
                      (< masked-current-cluster
                         (+ (count-of-clusters fat32$c)
                            *ms-first-data-cluster*)))))
  (b*
      (((mv dir-cc error-code)
        (get-cc fat32$c masked-current-cluster length))
       ((unless (equal error-code 0))
        (mv fat32$c error-code))
       (fat32$c
        (stobj-set-indices-in-fa-table
         fat32$c dir-cc
         (make-list (len dir-cc)
                    :initial-element 0))))
    (mv fat32$c 0)))

(defthm
  fat-length-of-clear-cc
  (equal
   (fat-length
    (mv-nth 0
            (clear-cc fat32$c
                      masked-current-cluster length)))
   (fat-length fat32$c))
  :hints (("goal" :in-theory (enable clear-cc))))

(defthm
  count-of-clusters-of-clear-cc
  (equal
   (count-of-clusters
    (mv-nth 0
            (clear-cc fat32$c
                      masked-current-cluster length)))
   (count-of-clusters fat32$c))
  :hints (("goal" :in-theory (enable clear-cc))))

(defthm
  lofat-fs-p-of-clear-cc
  (implies
   (lofat-fs-p fat32$c)
   (lofat-fs-p
    (mv-nth
     0
     (clear-cc fat32$c
               masked-current-cluster length))))
  :hints (("goal" :in-theory (enable clear-cc))))

(defthm
  cluster-size-of-clear-cc
  (equal
   (cluster-size
    (mv-nth 0
            (clear-cc fat32$c
                      masked-current-cluster length)))
   (cluster-size fat32$c))
  :hints (("goal" :in-theory (enable clear-cc))))

(defthm
  max-entry-count-of-clear-cc
  (equal (max-entry-count
          (mv-nth 0
                  (clear-cc fat32$c
                            masked-current-cluster length)))
         (max-entry-count fat32$c))
  :hints (("goal" :in-theory (enable clear-cc))))

(defthm
  pseudo-root-d-e-of-clear-cc
  (equal
   (pseudo-root-d-e
    (mv-nth 0
            (clear-cc fat32$c
                      masked-current-cluster length)))
   (pseudo-root-d-e fat32$c))
  :hints (("goal" :in-theory (enable clear-cc))))

;; This has to be disabled because it's causing fat32-build-index-list to
;; appear where it isn't wanted.
(defthmd
  clear-cc-correctness-1
  (implies
   (<= 2 masked-current-cluster)
   (equal
    (mv-nth 1
            (clear-cc fat32$c
                      masked-current-cluster length))
    (mv-nth 1
            (get-cc-contents
             fat32$c
             masked-current-cluster length))))
  :hints (("goal" :in-theory (enable clear-cc))))

(defthm
  clear-cc-correctness-2
  (implies
   (and
    (lofat-fs-p fat32$c)
    (non-free-index-listp x (effective-fat fat32$c))
    (not
     (intersectp-equal
      x
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32$c)
                                      masked-current-cluster length
                                      (cluster-size fat32$c))))))
   (non-free-index-listp
    x
    (effective-fat
     (mv-nth 0
             (clear-cc fat32$c
                       masked-current-cluster length)))))
  :hints (("goal" :in-theory (enable clear-cc))))

(defthmd clear-cc-correctness-3
  (implies
   (not (equal (mv-nth
                1
                (clear-cc
                 fat32$c masked-current-cluster length))
               0))
   (equal (mv-nth
           0
           (clear-cc
            fat32$c masked-current-cluster length))
          fat32$c))
  :hints (("goal" :in-theory (enable clear-cc))))

;; This is general.
(local
 (defthm
   clear-cc-reversibility-lemma-1
   (implies
    (equal (mv-nth 1
                   (fat32-build-index-list fa-table masked-current-cluster
                                           length cluster-size))
           0)
    (consp (mv-nth 0
                   (fat32-build-index-list fa-table masked-current-cluster
                                           length cluster-size))))
   :hints (("goal" :in-theory (enable fat32-build-index-list)))))

(defthm
  clear-cc-reversibility-lemma-2
  (implies
   (lofat-fs-p fat32$c)
   (equal
    (stobj-set-indices-in-fa-table
     fat32$c
     (mv-nth 0
             (fat32-build-index-list (effective-fat fat32$c)
                                     masked-current-cluster
                                     length (cluster-size fat32$c)))
     (append
      (cdr
       (mv-nth
        0
        (fat32-build-index-list (effective-fat fat32$c)
                                masked-current-cluster
                                length (cluster-size fat32$c))))
      (list
       (fat32-entry-mask
        (fati
         (car
          (last
           (mv-nth 0
                   (fat32-build-index-list (effective-fat fat32$c)
                                           masked-current-cluster length
                                           (cluster-size fat32$c)))))
         fat32$c)))))
    fat32$c))
  :hints
  (("goal"
    :in-theory
    (e/d
     (stobj-set-indices-in-fa-table fat32-build-index-list
                                    fat32-update-lower-28-of-fat32-entry-mask
                                    nfix)
     ((:rewrite get-cc-contents-correctness-2)))
    :induct (fat32-build-index-list (effective-fat fat32$c)
                                    masked-current-cluster
                                    length (cluster-size fat32$c))
    :expand
    (fat32-build-index-list
     (effective-fat fat32$c)
     (fat32-entry-mask (fati masked-current-cluster fat32$c))
     (+ length
        (- (cluster-size fat32$c)))
     (cluster-size fat32$c)))))

(defthm
  clear-cc-reversibility
  (implies
   (and (lofat-fs-p fat32$c)
        (fat32-masked-entry-p masked-current-cluster)
        (>= masked-current-cluster
            *ms-first-data-cluster*)
        (< masked-current-cluster
           (+ (count-of-clusters fat32$c)
              *ms-first-data-cluster*)))
   (equal
    (stobj-set-indices-in-fa-table
     (mv-nth 0
             (clear-cc fat32$c
                       masked-current-cluster length))
     (mv-nth 0
             (fat32-build-index-list (effective-fat fat32$c)
                                     masked-current-cluster
                                     length (cluster-size fat32$c)))
     (append
      (cdr
       (mv-nth
        0
        (fat32-build-index-list (effective-fat fat32$c)
                                masked-current-cluster
                                length (cluster-size fat32$c))))
      (list
       (fat32-entry-mask
        (fati
         (car
          (last
           (mv-nth 0
                   (fat32-build-index-list (effective-fat fat32$c)
                                           masked-current-cluster length
                                           (cluster-size fat32$c)))))
         fat32$c)))))
    fat32$c))
  :hints (("goal" :in-theory (e/d (clear-cc)
                                  (clear-cc-reversibility-lemma-2))
           :use clear-cc-reversibility-lemma-2
           :do-not-induct t)))

(encapsulate
  ()

  (local
   (defthm
     fat32-build-index-list-of-effective-fat-of-clear-cc-lemma-1
     (implies
      (and
       (<= (+ 2 (count-of-clusters fat32$c))
           first-cluster)
       (lofat-fs-p fat32$c)
       (fat32-masked-entry-p first-cluster)
       (fat32-masked-entry-p masked-current-cluster)
       (not
        (intersectp-equal
         (mv-nth 0
                 (fat32-build-index-list
                  (effective-fat fat32$c)
                  masked-current-cluster
                  length1 (cluster-size fat32$c)))
         (mv-nth 0
                 (fat32-build-index-list
                  (effective-fat fat32$c)
                  first-cluster length2 (cluster-size fat32$c))))))
      (equal
       (fat32-build-index-list
        (effective-fat
         (mv-nth 0
                 (clear-cc
                  fat32$c first-cluster length2)))
        masked-current-cluster
        length1 (cluster-size fat32$c))
       (fat32-build-index-list
        (effective-fat fat32$c)
        masked-current-cluster
        length1 (cluster-size fat32$c))))
     :hints
     (("goal"
       :in-theory (e/d (intersectp-equal clear-cc)
                       (intersectp-is-commutative))
       :expand
       ((fat32-build-index-list (effective-fat fat32$c)
                                first-cluster length2
                                (cluster-size fat32$c))
        (get-cc-contents
         fat32$c first-cluster length2))
       :use
       (:instance
        (:rewrite intersectp-is-commutative)
        (y
         (mv-nth
          0
          (fat32-build-index-list (effective-fat fat32$c)
                                  first-cluster length2
                                  (cluster-size fat32$c))))
        (x (mv-nth 0
                   (fat32-build-index-list
                    (effective-fat fat32$c)
                    masked-current-cluster length1
                    (cluster-size fat32$c)))))))))

  (defthm
    fat32-build-index-list-of-effective-fat-of-clear-cc
    (implies
     (and
      (lofat-fs-p fat32$c)
      (fat32-masked-entry-p masked-current-cluster1)
      (fat32-masked-entry-p masked-current-cluster2)
      (<= *ms-first-data-cluster*
          masked-current-cluster1)
      (not
       (intersectp-equal
        (mv-nth '0
                (fat32-build-index-list (effective-fat fat32$c)
                                        masked-current-cluster1
                                        length1 (cluster-size fat32$c)))
        (mv-nth '0
                (fat32-build-index-list (effective-fat fat32$c)
                                        masked-current-cluster2 length2
                                        (cluster-size fat32$c)))))
      (equal cluster-size (cluster-size fat32$c)))
     (equal
      (fat32-build-index-list
       (effective-fat
        (mv-nth 0
                (clear-cc fat32$c
                          masked-current-cluster1 length1)))
       masked-current-cluster2
       length2 cluster-size)
      (fat32-build-index-list (effective-fat fat32$c)
                              masked-current-cluster2 length2
                              cluster-size)))
    :hints (("goal" :cases ((<= (+ 2 (count-of-clusters fat32$c))
                                masked-current-cluster1)))
            ("subgoal 2" :in-theory (enable clear-cc)))))

(defthm
  d-e-cc-of-clear-cc
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-masked-entry-p masked-current-cluster)
    (d-e-p d-e)
    (<= *ms-first-data-cluster*
        masked-current-cluster)
    (not
     (intersectp-equal
      (mv-nth '0
              (fat32-build-index-list (effective-fat fat32$c)
                                      masked-current-cluster
                                      length (cluster-size fat32$c)))
      (mv-nth '0
              (d-e-cc fat32$c d-e)))))
   (equal (d-e-cc
           (mv-nth 0
                   (clear-cc fat32$c
                             masked-current-cluster length))
           d-e)
          (d-e-cc fat32$c d-e)))
  :hints (("goal" :in-theory (enable d-e-cc))))

(defthm
  effective-fat-of-clear-cc
  (implies
   (lofat-fs-p fat32$c)
   (equal
    (effective-fat
     (mv-nth 0
             (clear-cc fat32$c
                       masked-current-cluster length)))
    (if
        (equal (mv-nth 1
                       (clear-cc fat32$c
                                 masked-current-cluster length))
               0)
        (set-indices-in-fa-table
         (effective-fat fat32$c)
         (mv-nth 0
                 (fat32-build-index-list (effective-fat fat32$c)
                                         masked-current-cluster
                                         length (cluster-size fat32$c)))
         (make-list-ac
          (len
           (mv-nth
            0
            (fat32-build-index-list (effective-fat fat32$c)
                                    masked-current-cluster
                                    length (cluster-size fat32$c))))
          0 nil))
      (effective-fat fat32$c))))
  :hints (("goal" :in-theory (enable clear-cc)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32$c)
          (not (d-e-directory-p d-e))
          (equal masked-current-cluster
                 (d-e-first-cluster d-e))
          (equal length (d-e-file-size d-e)))
     (equal
      (effective-fat
       (mv-nth 0
               (clear-cc fat32$c
                         masked-current-cluster length)))
      (if
          (equal (mv-nth 1
                         (d-e-cc fat32$c d-e))
                 0)
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth 0
                   (d-e-cc fat32$c d-e))
           (make-list-ac
            (len (mv-nth 0
                         (d-e-cc fat32$c d-e)))
            0 nil))
        (effective-fat fat32$c))))
    :hints (("goal" :in-theory (enable d-e-cc
                                       clear-cc))))
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32$c)
          (d-e-directory-p d-e)
          (equal masked-current-cluster
                 (d-e-first-cluster d-e))
          (equal length *ms-max-dir-size*))
     (equal
      (effective-fat
       (mv-nth 0
               (clear-cc fat32$c
                         masked-current-cluster length)))
      (if
          (equal (mv-nth 1
                         (d-e-cc fat32$c d-e))
                 0)
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth 0
                   (d-e-cc fat32$c d-e))
           (make-list-ac
            (len (mv-nth 0
                         (d-e-cc fat32$c d-e)))
            0 nil))
        (effective-fat fat32$c))))
    :hints (("goal" :in-theory (enable d-e-cc
                                       clear-cc))))))

;; This is needed, to avoid introducing unwanted fat32-build-index-list terms
;; into proofs.
(in-theory (disable (:rewrite effective-fat-of-clear-cc . 1)))

(encapsulate
  ()

  (local
   (defthm
     get-cc-contents-of-clear-cc-lemma-1
     (implies
      (and
       (<= (+ 2 (count-of-clusters fat32$c))
           first-cluster)
       (lofat-fs-p fat32$c)
       (fat32-masked-entry-p first-cluster)
       (fat32-masked-entry-p masked-current-cluster)
       (not
        (intersectp-equal
         (mv-nth 0
                 (fat32-build-index-list
                  (effective-fat fat32$c)
                  masked-current-cluster
                  length1 (cluster-size fat32$c)))
         (mv-nth 0
                 (fat32-build-index-list
                  (effective-fat fat32$c)
                  first-cluster length2 (cluster-size fat32$c))))))
      (equal
       (get-cc-contents
        (mv-nth 0
                (clear-cc
                 fat32$c first-cluster length2))
        masked-current-cluster length1)
       (get-cc-contents
        fat32$c masked-current-cluster length1)))
     :hints
     (("goal"
       :in-theory (e/d (intersectp-equal clear-cc)
                       (intersectp-is-commutative))
       :expand
       ((fat32-build-index-list (effective-fat fat32$c)
                                first-cluster length2
                                (cluster-size fat32$c))
        (get-cc-contents
         fat32$c first-cluster length2))
       :use
       (:instance
        (:rewrite intersectp-is-commutative)
        (y
         (mv-nth
          0
          (fat32-build-index-list (effective-fat fat32$c)
                                  first-cluster length2
                                  (cluster-size fat32$c))))
        (x (mv-nth 0
                   (fat32-build-index-list
                    (effective-fat fat32$c)
                    masked-current-cluster length1
                    (cluster-size fat32$c)))))))))

  (defthm
    get-cc-contents-of-clear-cc
    (implies
     (and
      (lofat-fs-p fat32$c)
      (fat32-masked-entry-p masked-current-cluster1)
      (fat32-masked-entry-p masked-current-cluster2)
      (<= *ms-first-data-cluster*
          masked-current-cluster1)
      (not
       (intersectp-equal
        (mv-nth '0
                (fat32-build-index-list (effective-fat fat32$c)
                                        masked-current-cluster1
                                        length1 (cluster-size fat32$c)))
        (mv-nth '0
                (fat32-build-index-list (effective-fat fat32$c)
                                        masked-current-cluster2 length2
                                        (cluster-size fat32$c))))))
     (equal
      (get-cc-contents
       (mv-nth 0
               (clear-cc fat32$c
                         masked-current-cluster1 length1))
       masked-current-cluster2 length2)
      (get-cc-contents fat32$c
                       masked-current-cluster2 length2)))
    :hints (("goal" :cases ((<= (+ 2 (count-of-clusters fat32$c))
                                masked-current-cluster1)))
            ("subgoal 2" :in-theory (enable clear-cc)))))

(defthm
  d-e-cc-contents-of-clear-cc
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-masked-entry-p masked-current-cluster)
    (d-e-p d-e)
    (<= *ms-first-data-cluster*
        masked-current-cluster)
    (not
     (intersectp-equal
      (mv-nth '0
              (fat32-build-index-list (effective-fat fat32$c)
                                      masked-current-cluster
                                      length (cluster-size fat32$c)))
      (mv-nth '0
              (d-e-cc fat32$c d-e)))))
   (equal (d-e-cc-contents
           (mv-nth 0
                   (clear-cc fat32$c
                             masked-current-cluster length))
           d-e)
          (d-e-cc-contents fat32$c d-e)))
  :hints (("goal" :in-theory (enable d-e-cc
                                     d-e-cc-contents))))

;; Free variables, are they necessary?
(defthm
  fati-of-clear-cc
  (implies
   (and (lofat-fs-p fat32$c)
        (natp i)
        (fat32-masked-entry-p masked-current-cluster)
        (<= *ms-first-data-cluster*
            masked-current-cluster)
        (< masked-current-cluster
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c)))
        (< i
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c))))
   (equal
    (fati
     i
     (mv-nth
      0
      (clear-cc fat32$c
                masked-current-cluster length)))
    (if
        (and
         (equal
          (mv-nth 1
                  (fat32-build-index-list
                   (effective-fat fat32$c)
                   masked-current-cluster
                   length (cluster-size fat32$c)))
          0)
         (member-equal
          i
          (mv-nth 0
                  (fat32-build-index-list
                   (effective-fat fat32$c)
                   masked-current-cluster length
                   (cluster-size fat32$c)))))
        (fat32-update-lower-28 (fati i fat32$c)
                               0)
      (fati i fat32$c))))
  :hints
  (("goal"
    :in-theory (e/d (clear-cc)
                    ((:rewrite nth-of-effective-fat)))
    :use
    ((:instance
      (:rewrite nth-of-effective-fat)
      (fat32$c
       (stobj-set-indices-in-fa-table
        fat32$c
        (mv-nth 0
                (fat32-build-index-list
                 (effective-fat fat32$c)
                 masked-current-cluster
                 length (cluster-size fat32$c)))
        (make-list-ac
         (len
          (mv-nth 0
                  (fat32-build-index-list
                   (effective-fat fat32$c)
                   masked-current-cluster
                   length (cluster-size fat32$c))))
         0 nil)))
      (n i))
     (:instance (:rewrite nth-of-effective-fat)
                (fat32$c fat32$c)
                (n i)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32$c)
          (natp i)
          (fat32-masked-entry-p masked-current-cluster)
          (<= *ms-first-data-cluster*
              masked-current-cluster)
          (< masked-current-cluster
             (+ *ms-first-data-cluster*
                (count-of-clusters fat32$c)))
          (< i
             (+ *ms-first-data-cluster*
                (count-of-clusters fat32$c)))
          (not (d-e-directory-p d-e))
          (equal masked-current-cluster
                 (d-e-first-cluster d-e))
          (equal length (d-e-file-size d-e)))
     (equal
      (fati
       i
       (mv-nth
        0
        (clear-cc fat32$c
                  masked-current-cluster length)))
      (if
          (and
           (equal
            (mv-nth 1
                    (d-e-cc fat32$c d-e))
            0)
           (member-equal
            i
            (mv-nth
             0
             (d-e-cc fat32$c d-e))))
          (fat32-update-lower-28 (fati i fat32$c)
                                 0)
        (fati i fat32$c))))
    :hints (("goal" :in-theory (enable d-e-cc))))
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32$c)
          (natp i)
          (fat32-masked-entry-p masked-current-cluster)
          (<= *ms-first-data-cluster*
              masked-current-cluster)
          (< masked-current-cluster
             (+ *ms-first-data-cluster*
                (count-of-clusters fat32$c)))
          (< i
             (+ *ms-first-data-cluster*
                (count-of-clusters fat32$c)))
          (d-e-directory-p d-e)
          (equal masked-current-cluster
                 (d-e-first-cluster d-e))
          (equal length *ms-max-dir-size*))
     (equal
      (fati
       i
       (mv-nth
        0
        (clear-cc fat32$c
                  masked-current-cluster length)))
      (if
          (and
           (equal
            (mv-nth 1
                    (d-e-cc fat32$c d-e))
            0)
           (member-equal
            i
            (mv-nth
             0
             (d-e-cc fat32$c d-e))))
          (fat32-update-lower-28 (fati i fat32$c)
                                 0)
        (fati i fat32$c))))
    :hints
    (("goal" :in-theory (enable d-e-cc))))))

(in-theory (disable (:REWRITE FATI-OF-CLEAR-CC . 1)))

;; This function calls place-contents with a meaningless value of d-e,
;; because we know that for a well-formed directory, the contents will be
;; non-empty and so there's no way we're going to be returned a d-e with
;; the first cluster set to 0 (with the mask, of course...) so we don't care
;; about the value of d-e returned.
(defund
  update-dir-contents
  (fat32$c first-cluster dir-contents)
  (declare
   (xargs
    :stobjs fat32$c
    :guard (and (lofat-fs-p fat32$c)
                (fat32-masked-entry-p first-cluster)
                (<= *ms-first-data-cluster* first-cluster)
                (> (+ *ms-first-data-cluster*
                      (count-of-clusters fat32$c))
                   first-cluster)
                (stringp dir-contents))
    :guard-debug t
    :guard-hints
    (("goal"
      :expand (fat32-build-index-list
               (effective-fat fat32$c)
               first-cluster
               2097152 (cluster-size fat32$c))
      :in-theory
      (disable unsigned-byte-p
               (:linear non-negativity-of-car-of-last-when-nat-listp))
      :use
      ((:instance
        nat-listp-forward-to-integer-listp
        (x (mv-nth 0
                   (fat32-build-index-list
                    (effective-fat fat32$c)
                    first-cluster *ms-max-dir-size*
                    (cluster-size fat32$c)))))
       (:instance
        (:linear non-negativity-of-car-of-last-when-nat-listp)
        (l (mv-nth 0
                   (fat32-build-index-list
                    (effective-fat fat32$c)
                    first-cluster *ms-max-dir-size*
                    (cluster-size fat32$c))))))))))
  (b* (((mv cc &)
        (get-cc fat32$c first-cluster *ms-max-dir-size*))
       (last-value
        (fat32-entry-mask (fati (car (last cc))
                                fat32$c)))
       ((mv fat32$c error-code)
        (clear-cc fat32$c
                  first-cluster *ms-max-dir-size*))
       ((unless (equal error-code 0))
        (mv fat32$c *eio*))
       (fat32$c
        (update-fati first-cluster
                     (fat32-update-lower-28
                      (fati first-cluster fat32$c)
                      *ms-end-of-cc*)
                     fat32$c))
       ((unless (> (length dir-contents) 0))
        (mv fat32$c 0))
       ((mv fat32$c & error-code &)
        (place-contents fat32$c (d-e-fix nil)
                        dir-contents 0 first-cluster))
       ((when (equal error-code 0))
        (mv fat32$c 0))
       ;; Reversing the effects of clear-cc
       (fat32$c (stobj-set-indices-in-fa-table
                 fat32$c cc
                 (append (cdr cc)
                         (list last-value)))))
    (mv fat32$c error-code)))

(defthm
  count-of-clusters-of-update-dir-contents
  (equal
   (count-of-clusters
    (mv-nth
     0
     (update-dir-contents fat32$c
                          first-cluster dir-contents)))
   (count-of-clusters fat32$c))
  :hints (("goal" :in-theory (enable update-dir-contents))))

(defthm
  cluster-size-of-update-dir-contents
  (equal
   (cluster-size
    (mv-nth
     0
     (update-dir-contents fat32$c
                          first-cluster dir-contents)))
   (cluster-size fat32$c))
  :hints (("goal" :in-theory (enable update-dir-contents))))

(defthm
  lofat-fs-p-of-update-dir-contents
  (implies
   (and (lofat-fs-p fat32$c)
        (fat32-masked-entry-p first-cluster)
        (<= *ms-first-data-cluster* first-cluster)
        (> (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c))
           first-cluster)
        (stringp dir-contents))
   (lofat-fs-p
    (mv-nth 0
            (update-dir-contents fat32$c
                                 first-cluster dir-contents))))
  :hints (("goal" :in-theory (enable update-dir-contents
                                     clear-cc-correctness-1))))

(defthm
  fat32-build-index-list-of-effective-fat-of-update-dir-contents
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-masked-entry-p first-cluster)
    (<= *ms-first-data-cluster* first-cluster)
    (stringp dir-contents)
    (fat32-masked-entry-p masked-current-cluster)
    (<= *ms-first-data-cluster*
        masked-current-cluster)
    (not (intersectp-equal
          (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32$c)
                                          masked-current-cluster
                                          length (cluster-size fat32$c)))
          (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32$c)
                                          first-cluster *ms-max-dir-size*
                                          (cluster-size fat32$c)))))
    (equal (mv-nth 1
                   (fat32-build-index-list (effective-fat fat32$c)
                                           masked-current-cluster
                                           length (cluster-size fat32$c)))
           0)
    (equal cluster-size (cluster-size fat32$c)))
   (equal
    (fat32-build-index-list
     (effective-fat
      (mv-nth 0
              (update-dir-contents fat32$c first-cluster dir-contents)))
     masked-current-cluster
     length cluster-size)
    (fat32-build-index-list (effective-fat fat32$c)
                            masked-current-cluster
                            length cluster-size)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (update-dir-contents intersectp-equal clear-cc)
     (intersectp-is-commutative intersect-with-subset
                                (:rewrite consp-of-fat32-build-index-list)))
    :expand ((fat32-build-index-list (effective-fat fat32$c)
                                     first-cluster *ms-max-dir-size*
                                     (cluster-size fat32$c))
             (get-cc-contents fat32$c first-cluster 2097152))
    :use
    (:instance
     (:rewrite intersectp-is-commutative)
     (y (mv-nth 0
                (fat32-build-index-list (effective-fat fat32$c)
                                        first-cluster
                                        2097152 (cluster-size fat32$c))))
     (x (mv-nth 0
                (fat32-build-index-list (effective-fat fat32$c)
                                        masked-current-cluster
                                        length (cluster-size fat32$c))))))))

(defthm
  d-e-cc-of-update-dir-contents
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-masked-entry-p first-cluster)
    (<= *ms-first-data-cluster* first-cluster)
    (stringp dir-contents)
    (d-e-p d-e)
    (<= *ms-first-data-cluster*
        (d-e-first-cluster d-e))
    (not
     (intersectp-equal
      (mv-nth 0
              (d-e-cc fat32$c d-e))
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32$c)
                                      first-cluster *ms-max-dir-size*
                                      (cluster-size fat32$c)))))
    (equal (mv-nth 1
                   (d-e-cc fat32$c d-e))
           0))
   (equal (d-e-cc
           (mv-nth 0
                   (update-dir-contents fat32$c
                                        first-cluster dir-contents))
           d-e)
          (d-e-cc fat32$c d-e)))
  :hints (("goal" :in-theory (enable d-e-cc))))

(defthm
  max-entry-count-of-update-dir-contents
  (equal
   (max-entry-count (mv-nth 0
                            (update-dir-contents fat32$c
                                                 first-cluster dir-contents)))
   (max-entry-count fat32$c))
  :hints (("goal" :in-theory (enable update-dir-contents))))

(defthm
  pseudo-root-d-e-of-update-dir-contents
  (equal
   (pseudo-root-d-e
    (mv-nth 0
            (update-dir-contents fat32$c
                                 first-cluster dir-contents)))
   (pseudo-root-d-e fat32$c))
  :hints (("goal" :in-theory (enable update-dir-contents))))

(defthmd
  update-dir-contents-correctness-1
  (implies
   (and (lofat-fs-p fat32$c)
        (fat32-masked-entry-p first-cluster)
        (<= *ms-first-data-cluster* first-cluster)
        (> (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c))
           first-cluster)
        (not (equal (mv-nth 1
                            (update-dir-contents fat32$c
                                                 first-cluster dir-contents))
                    0)))
   (equal (mv-nth 0
                  (update-dir-contents fat32$c
                                       first-cluster dir-contents))
          fat32$c))
  :hints
  (("goal"
    :in-theory (e/d (update-dir-contents clear-cc-correctness-1
                                         clear-cc-correctness-3
                                         place-contents-correctness-1))
    :expand
    (len (mv-nth '0
                 (fat32-build-index-list (effective-fat fat32$c)
                                         first-cluster '2097152
                                         (cluster-size fat32$c)))))))

(defthm natp-of-update-dir-contents
  (natp (mv-nth 1
                (update-dir-contents fat32$c
                                     first-cluster dir-contents)))
  :rule-classes :type-prescription
  :hints (("goal" :in-theory (enable update-dir-contents))))

(defun
    delete-d-e (d-e-list filename)
  (declare (xargs :guard (and (fat32-filename-p filename)
                              (d-e-list-p d-e-list))
                  :guard-debug t))
  (b*
      (((when (atom d-e-list)) nil)
       (d-e (car d-e-list))
       ((when (equal (d-e-filename d-e)
                     filename))
        (delete-d-e (cdr d-e-list) filename)))
    (list* (d-e-fix d-e)
           (delete-d-e (cdr d-e-list)
                       filename))))

(defthm d-e-list-p-of-delete-d-e
  (d-e-list-p (delete-d-e d-e-list filename)))

(defthm len-of-delete-d-e
  (<= (len (delete-d-e d-e-list filename))
      (len d-e-list))
  :rule-classes :linear)

(defthm
  find-d-e-of-delete-d-e
  (implies
   (useful-d-e-list-p d-e-list)
   (equal (find-d-e (delete-d-e d-e-list filename1)
                    filename2)
          (if (equal filename1 filename2)
              (mv (d-e-fix nil) *enoent*)
            (find-d-e d-e-list filename2))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (useful-d-e-list-p d-e-filename len-when-d-e-p
                        nth-when->=-n-len-l)
     ((:rewrite d-e-filename-of-d-e-set-filename)
      (:rewrite string=>nats-of-nats=>string)
      (:rewrite nth-update-nth)))
    :induct (delete-d-e d-e-list filename1))
   ("subgoal *1/2"
    :use
    ((:instance
      (:rewrite d-e-filename-of-d-e-set-filename)
      (filename
       (nats=>string
        (update-nth
         0 0
         (string=>nats (d-e-filename (car d-e-list))))))
      (d-e (car d-e-list)))
     (:instance
      (:rewrite string=>nats-of-nats=>string)
      (nats
       (update-nth
        0 0
        (string=>nats
         (nats=>string (take 11 (car d-e-list)))))))
     (:instance (:rewrite string=>nats-of-nats=>string)
                (nats (take 11 (car d-e-list))))
     (:instance (:rewrite nth-update-nth)
                (l (take 11 (car d-e-list)))
                (val 0)
                (n 0)
                (m 0))))))

(defthm
  useful-d-e-list-p-of-delete-d-e
  (implies (useful-d-e-list-p d-e-list)
           (useful-d-e-list-p (delete-d-e d-e-list filename)))
  :hints (("goal" :in-theory (enable useful-d-e-list-p))))

(defthm
  delete-d-e-correctness-1
  (implies
   (not (equal (mv-nth 1 (find-d-e d-e-list filename))
               0))
   (equal (delete-d-e d-e-list filename)
          (d-e-list-fix d-e-list))))

(defthm
  hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3
  (implies
   (d-e-directory-p (mv-nth 0 (find-d-e d-e-list filename)))
   (equal (mv-nth 1 (find-d-e d-e-list filename))
          0)))

(encapsulate
  ()

  (local
   (defthmd
     hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-1
     (implies
      (and (useful-d-e-list-p d-e-list)
           (equal (mv-nth 3
                          (lofat-to-hifat-helper fat32$c
                                                 d-e-list entry-limit))
                  0)
           (equal (mv-nth 1 (find-d-e d-e-list filename))
                  0)
           (not (d-e-directory-p (mv-nth 0
                                         (find-d-e d-e-list filename)))))
      (<
       (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c
                                       (delete-d-e d-e-list filename)
                                       entry-limit)))
       (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit)))))
     :hints
     (("goal" :in-theory
       (e/d (lofat-to-hifat-helper hifat-entry-count
                                   lofat-to-hifat-helper-correctness-4)
            ((:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
             (:rewrite nth-of-effective-fat)
             (:definition assoc-equal)))))
     :rule-classes :linear))

  ;; This induction proof is becoming a sort of bag to hold many things at
  ;; once... because it relieves the
  ;; (equal (mv-nth 3 (lofat-to-hifat-helper ...)) 0) free-variable related
  ;; hypothesis that's needed by some of these other things.
  (local
   (defthmd
     hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-2
     (implies
      (and (useful-d-e-list-p d-e-list)
           (equal (mv-nth 3
                          (lofat-to-hifat-helper fat32$c
                                                 d-e-list entry-limit))
                  0)
           (d-e-directory-p (mv-nth 0
                                    (find-d-e d-e-list filename)))
           (not-intersectp-list
            x
            (mv-nth
             2
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit))))
      (and
       (<
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper fat32$c
                                        (delete-d-e d-e-list filename)
                                        entry-limit)))
        (-
         (hifat-entry-count
          (mv-nth 0
                  (lofat-to-hifat-helper fat32$c
                                         d-e-list entry-limit)))
         (hifat-entry-count
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents
                      fat32$c
                      (mv-nth 0
                              (find-d-e d-e-list filename)))))
            entry-limit)))))
       (equal
        (mv-nth
         3
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents
                    fat32$c
                    (mv-nth 0
                            (find-d-e d-e-list filename)))))
          entry-limit))
        0)
       (not-intersectp-list
        (mv-nth
         0
         (d-e-cc
          fat32$c
          (mv-nth 0
                  (find-d-e d-e-list filename))))
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents
             fat32$c
             (mv-nth 0
                     (find-d-e d-e-list filename)))))
          entry-limit)))
       (not-intersectp-list
        x
        (mv-nth
         2
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth
            0
            (d-e-cc-contents
             fat32$c
             (mv-nth 0
                     (find-d-e d-e-list filename)))))
          entry-limit)))))
     :hints
     (("goal" :in-theory
       (e/d (lofat-to-hifat-helper hifat-entry-count useful-d-e-list-p
                                   lofat-to-hifat-helper-correctness-4)
            ((:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
             (:rewrite nth-of-effective-fat)
             (:definition assoc-equal)
             (:rewrite subsetp-car-member)
             (:rewrite d-e-list-p-of-cdr-when-d-e-list-p)
             (:rewrite assoc-of-car-when-member)
             (:rewrite hifat-to-lofat-inversion-lemma-2)
             (:rewrite useful-d-e-list-p-of-cdr)
             (:rewrite m1-file-p-of-cdar-when-m1-file-alist-p)
             (:rewrite take-of-len-free)
             (:rewrite nats=>chars-of-take)
             (:rewrite not-intersectp-list-when-subsetp-1)
             (:rewrite d-e-p-when-member-equal-of-d-e-list-p)
             (:definition binary-append)
             (:rewrite subsetp-member . 1)
             (:rewrite member-of-append)))))))

  (defthm
    hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e
    (implies
     (and (useful-d-e-list-p d-e-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32$c
                                                d-e-list entry-limit))
                 0)
          (d-e-directory-p (mv-nth 0
                                   (find-d-e d-e-list filename))))
     (<
      (hifat-entry-count
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c
                                      (delete-d-e d-e-list filename)
                                      entry-limit)))
      (-
       (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit)))
       (hifat-entry-count
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents
                    fat32$c
                    (mv-nth 0
                            (find-d-e d-e-list filename)))))
          entry-limit))))))
    :hints
    (("goal" :use
      (:instance
       hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-2
       (x nil))))
    :rule-classes :linear)

  (defthm
    d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-1
    (implies
     (and (useful-d-e-list-p d-e-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32$c
                                                d-e-list entry-limit))
                 0)
          (d-e-directory-p (mv-nth 0
                                   (find-d-e d-e-list filename))))
     (not-intersectp-list
      (mv-nth
       0
       (d-e-cc
        fat32$c
        (mv-nth 0
                (find-d-e d-e-list filename))))
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           fat32$c
           (mv-nth 0
                   (find-d-e d-e-list filename)))))
        entry-limit))))
    :hints
    (("Goal" :use
      (:instance
       hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-2
       (x nil)))))

  (defthm
    d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-2
    (implies
     (and (useful-d-e-list-p d-e-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32$c
                                                d-e-list entry-limit))
                 0)
          (d-e-directory-p (mv-nth 0
                                   (find-d-e d-e-list filename)))
          (not-intersectp-list
           x
           (mv-nth
            2
            (lofat-to-hifat-helper fat32$c
                                   d-e-list entry-limit))))
     (not-intersectp-list
      x
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth
          0
          (d-e-cc-contents
           fat32$c
           (mv-nth 0
                   (find-d-e d-e-list filename)))))
        entry-limit))))
    :hints
    (("Goal" :use
      hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-2))))

;; Care should be taken before choosing to change this function's
;; definition. It has the very useful property that the length of the directory
;; contents remain the same, which means no reallocation is required.
(defund
  clear-d-e (dir-contents filename)
  (declare
   (xargs :measure (len dir-contents)
          :guard (and (fat32-filename-p filename)
                      (unsigned-byte-listp 8 dir-contents))
          :guard-hints (("goal" :in-theory (enable d-e-p)))
          :guard-debug t))
  (b*
      (((when (< (len dir-contents)
                 *ms-d-e-length*))
        dir-contents)
       (d-e (take *ms-d-e-length* dir-contents))
       ((when (equal (char (d-e-filename d-e) 0)
                     (code-char 0)))
        dir-contents)
       ((when (equal (d-e-filename d-e)
                     filename))
        (append
         (d-e-set-filename
          d-e
          (nats=>string
           (update-nth 0 229
                       (string=>nats (d-e-filename d-e)))))
         (clear-d-e (nthcdr *ms-d-e-length* dir-contents)
                    filename))))
    (append
     d-e
     (clear-d-e (nthcdr *ms-d-e-length* dir-contents)
                filename))))

(defthm
  len-of-clear-d-e
  (equal (len (clear-d-e dir-contents filename))
         (len dir-contents))
  :hints (("goal" :in-theory (enable len-when-d-e-p clear-d-e))))

(defthm
  unsigned-byte-listp-of-clear-d-e
  (implies
   (unsigned-byte-listp 8 dir-contents)
   (unsigned-byte-listp 8
                        (clear-d-e dir-contents filename)))
  :hints (("goal" :in-theory (enable clear-d-e))))

(defthm
  make-d-e-list-of-clear-d-e-lemma-1
  (implies
   (equal (char filename 0)
          (code-char #xe5))
   (useless-d-e-p (d-e-set-filename d-e filename)))
  :hints (("goal" :in-theory (enable useless-d-e-p))))

(defthm
  make-d-e-list-of-clear-d-e
  (equal
   (make-d-e-list (nats=>string (clear-d-e (string=>nats dir-contents)
                                           filename)))
   (delete-d-e (make-d-e-list dir-contents)
               filename))
  :hints (("goal" :in-theory (enable make-d-e-list d-e-fix
                                     clear-d-e
                                     len-when-d-e-p string=>nats
                                     nats=>string)
           :induct (make-d-e-list dir-contents)
           :expand (clear-d-e (chars=>nats (explode dir-contents))
                              filename))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (make-event
   `(defthm
      make-d-e-list-of-append-of-clear-d-e-1
      (implies
       (equal (mod (len (explode dir-contents))
                   *ms-d-e-length*)
              0)
       (equal
        (make-d-e-list
         (implode (append (nats=>chars (clear-d-e (string=>nats dir-contents)
                                                  filename))
                          (make-list-ac n ,(code-char 0) nil))))
        (delete-d-e (make-d-e-list dir-contents)
                    filename)))
      :hints
      (("goal" :induct (make-d-e-list dir-contents)
        :in-theory (e/d (make-d-e-list d-e-fix clear-d-e
                                       string=>nats))
        :expand ((make-d-e-list dir-contents)
                 (clear-d-e (chars=>nats (explode dir-contents))
                            filename)))))))

(defthm
  lofat-to-hifat-helper-of-clear-cc
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-masked-entry-p masked-current-cluster)
    (<= *ms-first-data-cluster*
        masked-current-cluster)
    (< masked-current-cluster
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32$c)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper fat32$c
                             d-e-list entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0
             (fat32-build-index-list
              (effective-fat fat32$c)
              masked-current-cluster
              length (cluster-size fat32$c)))
     (mv-nth
      2
      (lofat-to-hifat-helper fat32$c
                             d-e-list entry-limit))))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (clear-cc fat32$c
                       masked-current-cluster length))
     d-e-list entry-limit)
    (lofat-to-hifat-helper fat32$c
                           d-e-list entry-limit)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper clear-cc
                            lofat-to-hifat-helper-of-stobj-set-indices-in-fa-table)
     ((:rewrite nth-of-effective-fat))))))

(defund make-d-e-with-filename (filename)
  (declare
   (xargs
    :guard (and (stringp filename)
                (equal (length filename) 11))))
  (d-e-set-filename (d-e-fix nil) filename))

(defthm d-e-p-of-make-d-e-with-filename
  (d-e-p (make-d-e-with-filename filename))
  :hints (("goal" :in-theory (enable make-d-e-with-filename))))

(defthm
  not-d-e-directory-p-of-make-d-e-with-filename
  (implies (fat32-filename-p filename)
           (not (d-e-directory-p (make-d-e-with-filename filename))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable make-d-e-with-filename))))

(defthm
  d-e-first-cluster-of-make-d-e-with-filename
  (implies
   (fat32-filename-p filename)
   (equal (d-e-first-cluster (make-d-e-with-filename filename))
          0))
  :hints (("goal" :do-not-induct t
           :in-theory (enable make-d-e-with-filename))))

(defthm
  d-e-filename-of-make-d-e-with-filename
  (implies (fat32-filename-p filename)
           (equal (d-e-filename (make-d-e-with-filename filename))
                  filename))
  :hints (("goal" :do-not-induct t
           :in-theory (enable make-d-e-with-filename))))

(defthm
  get-cc-contents-of-update-dir-contents-disjoint
  (implies
   (and
    (lofat-fs-p fat32$c)
    (stringp dir-contents)
    (fat32-masked-entry-p masked-current-cluster)
    (not (< masked-current-cluster '2))
    (fat32-masked-entry-p first-cluster)
    (<= 2 first-cluster)
    (not
     (intersectp-equal
      (mv-nth '0
              (fat32-build-index-list (effective-fat fat32$c)
                                      first-cluster '2097152
                                      (cluster-size fat32$c)))
      (mv-nth '0
              (fat32-build-index-list (effective-fat fat32$c)
                                      masked-current-cluster
                                      length (cluster-size fat32$c)))))
    (equal (mv-nth '1
                   (get-cc-contents fat32$c masked-current-cluster length))
           '0))
   (equal
    (get-cc-contents
     (mv-nth 0
             (update-dir-contents fat32$c first-cluster dir-contents))
     masked-current-cluster length)
    (get-cc-contents fat32$c masked-current-cluster length)))
  :hints
  (("goal"
    :in-theory (e/d (update-dir-contents clear-cc-correctness-1)
                    ((:rewrite intersectp-is-commutative)
                     (:rewrite consp-of-fat32-build-index-list)))
    :expand
    ((fat32-build-index-list (effective-fat fat32$c)
                             first-cluster '2097152
                             (cluster-size fat32$c))
     (intersectp-equal
      nil
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32$c)
                                      masked-current-cluster
                                      length (cluster-size fat32$c))))
     (:free
      (y)
      (intersectp-equal
       (cons first-cluster y)
       (mv-nth 0
               (fat32-build-index-list (effective-fat fat32$c)
                                       masked-current-cluster
                                       length (cluster-size fat32$c)))))
     (get-cc-contents fat32$c first-cluster 2097152))
    :use
    ((:instance
      (:rewrite intersectp-is-commutative)
      (y (cons first-cluster
               (mv-nth 0
                       (fat32-build-index-list
                        (effective-fat fat32$c)
                        (fat32-entry-mask (fati first-cluster fat32$c))
                        (+ 2097152 (- (cluster-size fat32$c)))
                        (cluster-size fat32$c)))))
      (x (mv-nth 0
                 (fat32-build-index-list (effective-fat fat32$c)
                                         masked-current-cluster
                                         length (cluster-size fat32$c)))))
     (:instance
      (:rewrite intersectp-is-commutative)
      (y (cons first-cluster nil))
      (x (mv-nth 0
                 (fat32-build-index-list (effective-fat fat32$c)
                                         masked-current-cluster
                                         length (cluster-size fat32$c)))))))))

(local
 (defthm
   get-cc-contents-of-update-dir-contents-coincident-lemma-1
   (implies
    (and (lofat-fs-p fat32$c)
         (< 0 (len (explode dir-contents))))
    (not (< (binary-+ '-1
                      (len (make-clusters dir-contents
                                          (cluster-size fat32$c))))
            '0)))))

(defthmd
  get-cc-contents-of-update-dir-contents-coincident-lemma-2
  (implies
   (and (integerp first-cluster)
        (or (< first-cluster *ms-first-data-cluster*)
            (>= first-cluster
                (+ *ms-first-data-cluster*
                   (count-of-clusters fat32$c)))))
   (not
    (equal
     (mv-nth
      1
      (get-cc-contents fat32$c first-cluster 2097152))
     0)))
  :hints (("goal" :in-theory (enable nfix)
           :expand (get-cc-contents fat32$c
                                    first-cluster 2097152))))

(encapsulate
  ()

  (local
   (defthm
     lemma
     (implies
      (and
       (equal
        (mv-nth
         0
         (place-contents
          (update-fati
           first-cluster
           (fat32-update-lower-28 (fati first-cluster fat32$c)
                                  268435455)
           (mv-nth 0
                   (clear-cc fat32$c first-cluster 2097152)))
          '(0 0 0 0 0 0 0 0 0 0 0 0
              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          dir-contents 0 first-cluster))
        fat32$c)
       (<= 2 first-cluster)
       (< first-cluster
          (+ 2 (count-of-clusters fat32$c)))
       (lofat-fs-p fat32$c)
       (fat32-masked-entry-p first-cluster)
       (stringp dir-contents)
       (< 0 (len (explode dir-contents)))
       (<= (len (explode dir-contents))
           2097152)
       (equal
        (mv-nth
         2
         (place-contents
          (update-fati
           first-cluster
           (fat32-update-lower-28 (fati first-cluster fat32$c)
                                  268435455)
           (mv-nth 0
                   (clear-cc fat32$c first-cluster 2097152)))
          '(0 0 0 0 0 0 0 0 0 0 0 0
              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          dir-contents 0 first-cluster))
        0))
      (equal
       (get-cc-contents fat32$c first-cluster 2097152)
       (mv
        (implode
         (append
          (explode dir-contents)
          (make-list-ac
           (+ (- (len (explode dir-contents)))
              (* (cluster-size fat32$c)
                 (len (make-clusters dir-contents
                                     (cluster-size fat32$c)))))
           (code-char 0)
           nil)))
        0)))
     :hints
     (("goal"
       :in-theory
       (e/d
        (update-dir-contents
         (:linear hifat-to-lofat-inversion-lemma-16))
        ((:rewrite nth-of-set-indices-in-fa-table-when-member)
         (:rewrite get-cc-contents-of-place-contents-coincident)))
       :use
       ((:instance
         (:rewrite get-cc-contents-of-place-contents-coincident)
         (length *ms-max-dir-size*)
         (file-length 0)
         (contents dir-contents)
         (d-e (d-e-fix nil))
         (fat32$c
          (update-fati
           first-cluster
           (fat32-update-lower-28 (fati first-cluster fat32$c)
                                  268435455)
           (mv-nth 0
                   (clear-cc fat32$c
                             first-cluster *ms-max-dir-size*))))))))))

  ;; Hypotheses are minimal.
  (defthm
    get-cc-contents-of-update-dir-contents-coincident
    (implies
     (and
      (lofat-fs-p fat32$c)
      (fat32-masked-entry-p first-cluster)
      (stringp dir-contents)
      (< 0 (len (explode dir-contents)))
      (<= (len (explode dir-contents))
          *ms-max-dir-size*)
      (equal
       (mv-nth 1
               (get-cc-contents fat32$c
                                first-cluster *ms-max-dir-size*))
       0))
     (equal
      (get-cc-contents
       (mv-nth 0
               (update-dir-contents fat32$c
                                    first-cluster dir-contents))
       first-cluster *ms-max-dir-size*)
      (if
          (equal (mv-nth 1
                         (update-dir-contents fat32$c
                                              first-cluster dir-contents))
                 0)
          (mv
           (implode
            (append
             (explode dir-contents)
             (make-list-ac
              (+ (- (len (explode dir-contents)))
                 (* (cluster-size fat32$c)
                    (len (make-clusters dir-contents
                                        (cluster-size fat32$c)))))
              (code-char 0)
              nil)))
           0)
        (get-cc-contents fat32$c
                         first-cluster *ms-max-dir-size*))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (update-dir-contents
        (:linear hifat-to-lofat-inversion-lemma-16)
        (:rewrite fati-of-clear-cc . 1))
       ((:rewrite nth-of-set-indices-in-fa-table-when-member)))
      :use
      ((:instance
        (:rewrite nth-of-set-indices-in-fa-table-when-member)
        (val 0)
        (index-list
         (cons
          first-cluster
          (mv-nth 0
                  (fat32-build-index-list
                   (effective-fat fat32$c)
                   (fat32-entry-mask (fati first-cluster fat32$c))
                   (+ 2097152
                      (- (cluster-size fat32$c)))
                   (cluster-size fat32$c)))))
        (fa-table (effective-fat fat32$c))
        (n first-cluster))
       (:rewrite update-dir-contents-correctness-1)
       get-cc-contents-of-update-dir-contents-coincident-lemma-2)))))

(defthm
  d-e-cc-contents-of-update-dir-contents-disjoint
  (implies
   (and
    (lofat-fs-p fat32$c)
    (stringp dir-contents)
    (d-e-p d-e)
    (<= *ms-first-data-cluster*
        (d-e-first-cluster d-e))
    (fat32-masked-entry-p first-cluster)
    (<= 2 first-cluster)
    (not (intersectp-equal
          (mv-nth '0
                  (fat32-build-index-list (effective-fat fat32$c)
                                          first-cluster '2097152
                                          (cluster-size fat32$c)))
          (mv-nth '0
                  (d-e-cc fat32$c d-e))))
    (equal (mv-nth '1
                   (d-e-cc-contents fat32$c d-e))
           '0))
   (equal (d-e-cc-contents
           (mv-nth 0
                   (update-dir-contents fat32$c
                                        first-cluster dir-contents))
           d-e)
          (d-e-cc-contents fat32$c d-e)))
  :hints (("goal" :in-theory (enable d-e-cc
                                     d-e-cc-contents))))

;; Hypotheses are minimal.
(defthm
  d-e-cc-contents-of-update-dir-contents-coincident
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-masked-entry-p first-cluster)
    (< 0 (len (explode dir-contents)))
    (<= (len (explode dir-contents))
        *ms-max-dir-size*)
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c d-e))
           0)
    (equal (d-e-first-cluster d-e)
           first-cluster)
    (d-e-directory-p d-e))
   (equal
    (d-e-cc-contents
     (mv-nth 0
             (update-dir-contents fat32$c
                                  first-cluster dir-contents))
     d-e)
    (if
        (equal (mv-nth 1
                       (update-dir-contents fat32$c
                                            first-cluster dir-contents))
               0)
        (mv
         (implode
          (append
           (explode dir-contents)
           (make-list-ac
            (+ (- (len (explode dir-contents)))
               (* (cluster-size fat32$c)
                  (len (make-clusters dir-contents
                                      (cluster-size fat32$c)))))
            (code-char 0)
            nil)))
         0)
      (d-e-cc-contents
       fat32$c
       d-e))))
  :hints
  (("goal" :in-theory
    (e/d (d-e-cc-contents)
         (get-cc-contents-of-update-dir-contents-coincident))
    :use get-cc-contents-of-update-dir-contents-coincident)))

(defthm
  lofat-to-hifat-helper-of-update-dir-contents
  (implies
   (and (useful-d-e-list-p d-e-list)
        (lofat-fs-p fat32$c)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0)
        (fat32-masked-entry-p first-cluster)
        (<= *ms-first-data-cluster* first-cluster)
        (stringp dir-contents)
        (not-intersectp-list
         (mv-nth 0
                 (fat32-build-index-list (effective-fat fat32$c)
                                         first-cluster *ms-max-dir-size*
                                         (cluster-size fat32$c)))
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c
                                        d-e-list entry-limit))))
   (equal (lofat-to-hifat-helper
           (mv-nth 0
                   (update-dir-contents fat32$c
                                        first-cluster dir-contents))
           d-e-list entry-limit)
          (lofat-to-hifat-helper fat32$c
                                 d-e-list entry-limit)))
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper
                                     not-intersectp-list)
           :induct (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit))))

;; Slightly better version of
;; d-e-cc-contents-of-update-dir-contents-disjoint.
(defthm
  d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-3
  (implies
   (and
    (lofat-fs-p fat32$c)
    (stringp dir-contents)
    (d-e-p d-e)
    (<= *ms-first-data-cluster*
        (d-e-first-cluster d-e))
    (d-e-p root-d-e)
    (d-e-directory-p root-d-e)
    (<= 2 (d-e-first-cluster root-d-e))
    (case-split
     (not (intersectp-equal
           (mv-nth '0
                   (d-e-cc fat32$c root-d-e))
           (mv-nth '0
                   (d-e-cc fat32$c d-e)))))
    (equal (mv-nth '1
                   (d-e-cc-contents fat32$c d-e))
           '0))
   (equal
    (d-e-cc-contents
     (mv-nth 0
             (update-dir-contents fat32$c
                                  (d-e-first-cluster root-d-e)
                                  dir-contents))
     d-e)
    (d-e-cc-contents fat32$c d-e)))
  :hints
  (("goal"
    :in-theory
    (e/d (d-e-cc)
         (d-e-cc-contents-of-update-dir-contents-disjoint))
    :use
    (:instance d-e-cc-contents-of-update-dir-contents-disjoint
               (first-cluster (d-e-first-cluster root-d-e))))))

;; Slightly better version of d-e-cc-of-update-dir-contents.
(defthm
  d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-11
  (implies
   (and
    (lofat-fs-p fat32$c)
    (stringp dir-contents)
    (d-e-p d-e)
    (<= *ms-first-data-cluster*
        (d-e-first-cluster d-e))
    (d-e-p root-d-e)
    (d-e-directory-p root-d-e)
    (<= 2 (d-e-first-cluster root-d-e))
    (not (intersectp-equal
          (mv-nth '0
                  (d-e-cc fat32$c root-d-e))
          (mv-nth '0
                  (d-e-cc fat32$c d-e))))
    (equal (mv-nth '1
                   (d-e-cc-contents fat32$c d-e))
           '0))
   (equal
    (d-e-cc
     (mv-nth 0
             (update-dir-contents fat32$c
                                  (d-e-first-cluster root-d-e)
                                  dir-contents))
     d-e)
    (d-e-cc fat32$c d-e)))
  :hints
  (("goal"
    :in-theory (e/d (d-e-cc d-e-cc-contents)
                    (d-e-cc-of-update-dir-contents))
    :use (:instance d-e-cc-of-update-dir-contents
                    (first-cluster (d-e-first-cluster root-d-e))))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-4
  (implies
   (and
    (useful-d-e-list-p d-e-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit))
           0)
    (>=
     (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename)))
     *ms-first-data-cluster*)
    (> (+ *ms-first-data-cluster*
          (count-of-clusters fat32$c))
       (d-e-first-cluster (mv-nth 0
                                  (find-d-e d-e-list filename)))))
   (and
    (equal (mv-nth 1
                   (d-e-cc-contents
                    fat32$c
                    (mv-nth 0
                            (find-d-e d-e-list filename))))
           0)
    (no-duplicatesp-equal
     (mv-nth
      0
      (d-e-cc fat32$c
              (mv-nth 0
                      (find-d-e d-e-list filename)))))))
  :hints
  (("goal" :in-theory
    (e/d (lofat-to-hifat-helper)
         (nth-of-effective-fat (:definition no-duplicatesp-equal))))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-12
  (implies
   (equal (mv-nth 1
                  (d-e-cc-contents fat32$c d-e))
          0)
   (and (<= *ms-first-data-cluster*
            (d-e-first-cluster d-e))
        (< (d-e-first-cluster d-e)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c)))))
  :hints
  (("goal" :in-theory (enable d-e-cc-contents nfix)
    :expand ((get-cc-contents fat32$c
                              (d-e-first-cluster d-e)
                              (d-e-file-size d-e))
             (get-cc-contents fat32$c
                              (d-e-first-cluster d-e)
                              2097152))))
  :rule-classes :linear)

(defthm
  d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
  (implies
   (and
    (not-intersectp-list
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit)))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit))
           0)
    (d-e-list-p d-e-list)
    (<=
     2
     (d-e-first-cluster (mv-nth 0
                                (find-d-e d-e-list filename))))
    (<
     (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename)))
     (+ 2 (count-of-clusters fat32$c))))
   (not (intersectp-equal
         x
         (mv-nth '0
                 (d-e-cc
                  fat32$c
                  (mv-nth '0
                          (find-d-e d-e-list filename)))))))
  :hints (("goal" :in-theory (e/d (lofat-to-hifat-helper not-intersectp-list)
                                  ((:rewrite nth-of-effective-fat)))
           :expand ((:free (x) (intersectp-equal nil x)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c
                                      d-e-list entry-limit)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c
                                            d-e-list entry-limit))
             0)
      (d-e-list-p d-e-list)
      (not
       (d-e-directory-p (mv-nth 0
                                (find-d-e d-e-list filename))))
      (<=
       2
       (d-e-first-cluster (mv-nth 0
                                  (find-d-e d-e-list filename))))
      (< (d-e-first-cluster
          (mv-nth 0 (find-d-e d-e-list filename)))
         (+ 2 (count-of-clusters fat32$c))))
     (not
      (intersectp-equal
       x
       (mv-nth
        '0
        (fat32-build-index-list
         (effective-fat fat32$c)
         (d-e-first-cluster
          (mv-nth '0
                  (find-d-e d-e-list filename)))
         (d-e-file-size (mv-nth '0
                                (find-d-e d-e-list filename)))
         (cluster-size fat32$c))))))
    :hints (("goal" :in-theory (enable d-e-cc))))
   (:rewrite
    :corollary
    (implies
     (and
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c
                                      d-e-list entry-limit)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c
                                            d-e-list entry-limit))
             0)
      (d-e-list-p d-e-list)
      (d-e-directory-p (mv-nth 0 (find-d-e d-e-list filename)))
      (<=
       2
       (d-e-first-cluster (mv-nth 0
                                  (find-d-e d-e-list filename))))
      (< (d-e-first-cluster
          (mv-nth 0 (find-d-e d-e-list filename)))
         (+ 2 (count-of-clusters fat32$c))))
     (not
      (intersectp-equal
       x
       (mv-nth '0
               (fat32-build-index-list
                (effective-fat fat32$c)
                (d-e-first-cluster
                 (mv-nth '0
                         (find-d-e d-e-list filename)))
                *ms-max-dir-size*
                (cluster-size fat32$c))))))
    :hints (("goal" :in-theory (e/d (d-e-cc)))))
   (:rewrite
    :corollary
    (implies
     (and
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c
                                      d-e-list entry-limit)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c
                                            d-e-list entry-limit))
             0)
      (d-e-list-p d-e-list)
      (<=
       2
       (d-e-first-cluster (mv-nth 0
                                  (find-d-e d-e-list filename))))
      (<
       (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename)))
       (+ 2 (count-of-clusters fat32$c))))
     (not (intersectp-equal
           (mv-nth '0
                   (d-e-cc
                    fat32$c
                    (mv-nth '0
                            (find-d-e d-e-list filename))))
           x))))
   (:rewrite
    :corollary
    (implies
     (and
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c
                                      d-e-list entry-limit)))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c
                                            d-e-list entry-limit))
             0)
      (d-e-list-p d-e-list)
      (<=
       2
       (d-e-first-cluster (mv-nth 0
                                  (find-d-e d-e-list filename))))
      (<
       (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename)))
       (+ 2 (count-of-clusters fat32$c)))
      (case-split
       (member-equal a x)))
     (not (member-equal
           a
           (mv-nth '0
                   (d-e-cc
                    fat32$c
                    (mv-nth '0
                            (find-d-e d-e-list filename))))))))))

(defthm
  root-d-e-list-of-update-dir-contents
  (implies
   (and
    (lofat-fs-p fat32$c)
    (d-e-p d-e)
    (d-e-directory-p d-e)
    (<= *ms-first-data-cluster*
        (d-e-first-cluster d-e))
    (stringp dir-contents)
    (equal (mv-nth 1 (root-d-e-list fat32$c))
           0)
    (not
     (intersectp-equal
      (mv-nth 0
              (d-e-cc fat32$c d-e))
      (mv-nth 0
              (d-e-cc fat32$c
                      (pseudo-root-d-e fat32$c))))))
   (equal (root-d-e-list
           (mv-nth 0
                   (update-dir-contents fat32$c
                                        (d-e-first-cluster d-e)
                                        dir-contents)))
          (root-d-e-list fat32$c)))
  :hints (("goal" :in-theory (enable root-d-e-list))))

(defthm
  subdir-contents-p-when-zero-length
  (implies (and (stringp contents) (equal (len (explode contents)) 0))
           (not (subdir-contents-p contents)))
  :hints (("goal" :in-theory (enable subdir-contents-p remove1-d-e))))

;; It looks like this lemma needs to have its hypothesis about
;; (mv-nth 3 (lofat-to-hifat-helper ...)) in order to make its feeble but
;; sufficient claim about non-duplication of clusterchains...
(defthm
  get-cc-contents-of-lofat-remove-file-coincident-lemma-5
  (implies
   (and
    (d-e-list-p d-e-list)
    (<= 2
        (d-e-first-cluster
         (mv-nth 0
                 (find-d-e d-e-list filename))))
    (< (d-e-first-cluster
        (mv-nth 0 (find-d-e d-e-list filename)))
       (+ 2 (count-of-clusters fat32$c)))
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit))
     0)
    (not-intersectp-list
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit))))
   (not
    (intersectp-equal
     x
     (mv-nth
      0
      (d-e-cc
       fat32$c
       (mv-nth 0
               (find-d-e d-e-list filename)))))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper not-intersectp-list)
     ((:rewrite nth-of-effective-fat)
      (:rewrite integerp-of-car-when-integer-listp)
      (:definition integer-listp)
      (:definition len)))
    :induct t))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (d-e-list-p d-e-list)
      (<= 2
          (d-e-first-cluster
           (mv-nth 0
                   (find-d-e d-e-list filename))))
      (< (d-e-first-cluster
          (mv-nth 0 (find-d-e d-e-list filename)))
         (+ 2 (count-of-clusters fat32$c)))
      (d-e-directory-p
       (mv-nth 0 (find-d-e d-e-list filename)))
      (equal
       (mv-nth 3
               (lofat-to-hifat-helper fat32$c
                                      d-e-list entry-limit))
       0)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper fat32$c
                               d-e-list entry-limit))))
     (not
      (intersectp-equal
       x
       (mv-nth
        0
        (fat32-build-index-list
         (effective-fat fat32$c)
         (d-e-first-cluster
          (mv-nth 0 (find-d-e d-e-list filename)))
         *ms-max-dir-size*
         (cluster-size fat32$c))))))
    :hints
    (("goal" :in-theory (enable d-e-cc))))
   (:rewrite
    :corollary
    (implies
     (and
      (d-e-list-p d-e-list)
      (<= 2
          (d-e-first-cluster
           (mv-nth 0
                   (find-d-e d-e-list filename))))
      (< (d-e-first-cluster
          (mv-nth 0 (find-d-e d-e-list filename)))
         (+ 2 (count-of-clusters fat32$c)))
      (not (d-e-directory-p
            (mv-nth 0 (find-d-e d-e-list filename))))
      (equal
       (mv-nth 3
               (lofat-to-hifat-helper fat32$c
                                      d-e-list entry-limit))
       0)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper fat32$c
                               d-e-list entry-limit))))
     (not
      (intersectp-equal
       x
       (mv-nth
        0
        (fat32-build-index-list
         (effective-fat fat32$c)
         (d-e-first-cluster
          (mv-nth 0 (find-d-e d-e-list filename)))
         (d-e-file-size
          (mv-nth 0 (find-d-e d-e-list filename)))
         (cluster-size fat32$c))))))
    :hints
    (("goal" :in-theory (enable d-e-cc))))))

;; Slightly better version of d-e-cc-of-clear-cc.
(defthm
  d-e-cc-contents-of-lofat-remove-file-coincident-lemma-1
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-p d-e2)
        (d-e-p d-e1)
        (d-e-directory-p d-e1)
        (<= *ms-first-data-cluster*
            (d-e-first-cluster d-e1))
        (not (intersectp-equal
              (mv-nth '0
                      (d-e-cc fat32$c d-e1))
              (mv-nth '0
                      (d-e-cc fat32$c d-e2)))))
   (equal (d-e-cc
           (mv-nth 0
                   (clear-cc fat32$c
                             (d-e-first-cluster d-e1)
                             *ms-max-dir-size*))
           d-e2)
          (d-e-cc fat32$c d-e2)))
  :hints
  (("goal"
    :in-theory (e/d (d-e-cc)
                    (d-e-cc-of-clear-cc))
    :use (:instance d-e-cc-of-clear-cc
                    (d-e d-e2)
                    (masked-current-cluster (d-e-first-cluster d-e1))
                    (length *ms-max-dir-size*)))))

;; Slightly better version of d-e-cc-of-clear-cc.
(defthm
  d-e-cc-contents-of-lofat-remove-file-coincident-lemma-2
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-p d-e2)
        (d-e-p d-e1)
        (not (d-e-directory-p d-e1))
        (<= *ms-first-data-cluster*
            (d-e-first-cluster d-e1))
        (not (intersectp-equal
              (mv-nth '0
                      (d-e-cc fat32$c d-e1))
              (mv-nth '0
                      (d-e-cc fat32$c d-e2)))))
   (equal (d-e-cc
           (mv-nth 0
                   (clear-cc fat32$c
                             (d-e-first-cluster d-e1)
                             (d-e-file-size d-e1)))
           d-e2)
          (d-e-cc fat32$c d-e2)))
  :hints
  (("goal"
    :in-theory (e/d (d-e-cc)
                    (d-e-cc-of-clear-cc))
    :use (:instance d-e-cc-of-clear-cc
                    (d-e d-e2)
                    (masked-current-cluster (d-e-first-cluster d-e1))
                    (length (d-e-file-size d-e1))))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-coincident-lemma-7
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-directory-p d-e)
        (not (intersectp-equal
              x
              (mv-nth 0
                      (d-e-cc fat32$c d-e)))))
   (not (member-equal (d-e-first-cluster d-e)
                      x)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable intersectp-is-commutative)
    :expand
    ((:with intersectp-is-commutative
            (:free (y)
                   (intersectp-equal x
                                     (cons (d-e-first-cluster d-e)
                                           y))))
     (d-e-cc fat32$c d-e)
     (fat32-build-index-list (effective-fat fat32$c)
                             (d-e-first-cluster d-e)
                             2097152 (cluster-size fat32$c))
     (:free (y)
            (intersectp-equal (cons (d-e-first-cluster d-e) y)
                              x))))))

(defthm
  d-e-cc-contents-of-lofat-remove-file-coincident-lemma-9
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (<= *ms-first-data-cluster*
            (d-e-first-cluster d-e))
        (< (d-e-first-cluster d-e)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c)))
        (equal (mv-nth 1
                       (update-dir-contents fat32$c
                                            (d-e-first-cluster d-e)
                                            dir-contents))
               0)
        (stringp dir-contents)
        (< 0 (len (explode dir-contents)))
        (<= (len (explode dir-contents))
            *ms-max-dir-size*)
        (non-free-index-listp x (effective-fat fat32$c))
        (not (intersectp-equal
              x
              (mv-nth '0
                      (d-e-cc fat32$c d-e)))))
   (and
    (non-free-index-listp
     x
     (effective-fat
      (mv-nth 0
              (update-dir-contents fat32$c
                                   (d-e-first-cluster d-e)
                                   dir-contents))))
    (not
     (intersectp-equal
      x
      (mv-nth
       0
       (d-e-cc
        (mv-nth 0
                (update-dir-contents fat32$c
                                     (d-e-first-cluster d-e)
                                     dir-contents))
        d-e))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (update-dir-contents)
         (intersectp-is-commutative (:definition non-free-index-listp)
                                    (:definition stobj-set-clusters)))
    :expand
    ((:with intersectp-is-commutative
            (:free (y)
                   (intersectp-equal x
                                     (cons (d-e-first-cluster d-e)
                                           y))))
     (:with intersectp-is-commutative
            (intersectp-equal
             (mv-nth '0
                     (d-e-cc fat32$c d-e))
             x))
     (:free (y)
            (intersectp-equal (cons (d-e-first-cluster d-e) y)
                              x)))
    :cases
    ((equal (mv-nth '1
                    (d-e-cc-contents fat32$c d-e))
            '0)))))

;; Nice!
(defthm
  d-e-cc-contents-of-lofat-remove-file-coincident-lemma-8
  (implies
   (equal (mv-nth 1
                  (d-e-cc-contents fat32$c d-e))
          0)
   (consp (mv-nth 0
                  (d-e-cc fat32$c d-e))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (enable d-e-cc-contents
                       d-e-cc
                       get-cc-contents
                       fat32-build-index-list)
    :expand ((fat32-build-index-list (effective-fat fat32$c)
                                     (d-e-first-cluster d-e)
                                     2097152 (cluster-size fat32$c))
             (get-cc-contents fat32$c
                              (d-e-first-cluster d-e)
                              2097152)
             (fat32-build-index-list (effective-fat fat32$c)
                                     (d-e-first-cluster d-e)
                                     (d-e-file-size d-e)
                                     (cluster-size fat32$c))
             (get-cc-contents fat32$c
                              (d-e-first-cluster d-e)
                              (d-e-file-size d-e))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm
    root-d-e-list-of-lofat-remove-file-coincident-lemma-1
    (implies
     (and (lofat-fs-p fat32$c)
          (equal (mod length (cluster-size fat32$c))
                 0)
          (not (zp y))
          (equal (mod (cluster-size fat32$c) y)
                 0))
     (equal
      (mod
       (len
        (explode
         (mv-nth 0
                 (get-cc-contents fat32$c
                                  masked-current-cluster length))))
       y)
      0))
    :hints
    (("goal" :induct (get-cc-contents fat32$c
                                      masked-current-cluster length)
      :in-theory (enable get-cc-contents
                         nfix mod-sum-cases)))))

(defthm
  root-d-e-list-of-lofat-remove-file-coincident-lemma-2
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-directory-p d-e)
        (not (zp y))
        (equal (mod (cluster-size fat32$c) y)
               0))
   (equal
    (mod
     (len
      (explode
       (mv-nth 0
               (d-e-cc-contents fat32$c d-e))))
     y)
    0))
  :hints (("goal" :in-theory (enable d-e-cc-contents))))
(defthm
  lofat-to-hifat-helper-of-delete-d-e-1
  (implies
   (and
    (useful-d-e-list-p d-e-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit))
           0)
    (not-intersectp-list
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit))))
   (not-intersectp-list
    x
    (mv-nth 2
            (lofat-to-hifat-helper fat32$c
                                   (delete-d-e d-e-list filename)
                                   entry-limit))))
  :hints
  (("goal" :in-theory
    (e/d
     (lofat-to-hifat-helper lofat-to-hifat-helper-correctness-4
                            not-intersectp-list)
     ((:rewrite nth-of-effective-fat)
      (:definition assoc-equal)))
    :induct (lofat-to-hifat-helper fat32$c
                                   d-e-list entry-limit))))

(defthm
  lofat-to-hifat-helper-of-delete-d-e-2
  (implies
   (and (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0)
        (not (member-intersectp-equal
              x
              (mv-nth 2
                      (lofat-to-hifat-helper fat32$c
                                             d-e-list entry-limit)))))
   (not
    (member-intersectp-equal
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c
                                    (delete-d-e d-e-list filename)
                                    entry-limit)))))
  :hints
  (("goal"
    :in-theory (disable (:induction delete-d-e))
    :induct
    (member-intersectp-equal
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c
                                    (delete-d-e d-e-list filename)
                                    entry-limit)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (useful-d-e-list-p d-e-list)
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32$c
                                                d-e-list entry-limit))
                 0)
          (not (member-intersectp-equal
                x
                (mv-nth 2
                        (lofat-to-hifat-helper fat32$c
                                               d-e-list entry-limit)))))
     (not
      (member-intersectp-equal
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c
                                      (delete-d-e d-e-list filename)
                                      entry-limit))
       x))))))

(defthm
  lofat-to-hifat-helper-of-delete-d-e-3
  (implies
   (and (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0))
   (and
    (equal
     (mv-nth 0
             (lofat-to-hifat-helper fat32$c
                                    (delete-d-e d-e-list filename)
                                    entry-limit))
     (remove-assoc-equal
      filename
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c
                                     d-e-list entry-limit))))
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper fat32$c
                                    (delete-d-e d-e-list filename)
                                    entry-limit))
     0)))
  :hints
  (("goal" :in-theory
    (e/d (lofat-to-hifat-helper lofat-to-hifat-helper-correctness-4)
         (nth-of-effective-fat))
    :induct (lofat-to-hifat-helper fat32$c
                                   d-e-list entry-limit))))

(defthm
  lofat-to-hifat-helper-after-delete-and-clear-1-lemma-1
  (implies
   (and (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0)
        (d-e-directory-p (mv-nth 0
                                 (find-d-e d-e-list filename))))
   (and
    (<= *ms-first-data-cluster*
        (d-e-first-cluster (mv-nth 0
                                   (find-d-e d-e-list filename))))
    (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename)))
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32$c)))))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable lofat-to-hifat-helper))))

(defthm
  lofat-to-hifat-helper-after-delete-and-clear-2-lemma-2
  (implies
   (and
    (useful-d-e-list-p d-e-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
           0)
    (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename)))
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32$c)))
    (<= *ms-first-data-cluster*
        (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename))))
    (not (member-intersectp-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
          l)))
   (not-intersectp-list
    (mv-nth 0
            (d-e-cc fat32$c
                    (mv-nth 0 (find-d-e d-e-list filename))))
    l))
  :hints
  (("goal"
    :induct (lofat-to-hifat-helper fat32$c d-e-list entry-limit)
    :in-theory
    (e/d
     (lofat-to-hifat-helper)
     (member-intersectp-is-commutative (:rewrite nth-of-effective-fat))))))

(defthm
  lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-1
  (implies
   (and
    (not
     (member-intersectp-equal
      x
      (mv-nth
       2
       (lofat-to-hifat-helper fat32$c
                              d-e-list entry-limit))))
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit))
     0)
    (d-e-directory-p
     (mv-nth 0 (find-d-e d-e-list filename)))
    (useful-d-e-list-p d-e-list))
   (not
    (member-intersectp-equal
     x
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth
         0
         (d-e-cc-contents
          fat32$c
          (mv-nth 0
                  (find-d-e d-e-list filename)))))
       entry-limit)))))
  :hints
  (("goal" :in-theory (e/d (lofat-to-hifat-helper-correctness-4))
    :induct
    (member-intersectp-equal
     x
     (mv-nth
      2
      (lofat-to-hifat-helper fat32$c
                             d-e-list entry-limit)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (not
       (member-intersectp-equal
        x
        (mv-nth
         2
         (lofat-to-hifat-helper fat32$c
                                d-e-list entry-limit))))
      (equal
       (mv-nth 3
               (lofat-to-hifat-helper fat32$c
                                      d-e-list entry-limit))
       0)
      (d-e-directory-p
       (mv-nth 0 (find-d-e d-e-list filename)))
      (useful-d-e-list-p d-e-list))
     (not
      (member-intersectp-equal
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth
           0
           (get-cc-contents
            fat32$c
            (d-e-first-cluster
             (mv-nth 0 (find-d-e d-e-list filename)))
            *ms-max-dir-size*)))
         entry-limit)))))
    :hints
    (("goal"
      :in-theory (enable d-e-cc-contents))))))

;; Slightly better than lofat-to-hifat-helper-of-update-dir-contents
(defthm
  lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-2
  (implies
   (and (useful-d-e-list-p d-e-list)
        (lofat-fs-p fat32$c)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0)
        (d-e-p root-d-e)
        (d-e-directory-p root-d-e)
        (<= *ms-first-data-cluster*
            (d-e-first-cluster root-d-e))
        (stringp dir-contents)
        (not-intersectp-list
         (mv-nth 0
                 (d-e-cc fat32$c root-d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c
                                        d-e-list entry-limit))))
   (equal
    (lofat-to-hifat-helper
     (mv-nth 0
             (update-dir-contents fat32$c
                                  (d-e-first-cluster root-d-e)
                                  dir-contents))
     d-e-list entry-limit)
    (lofat-to-hifat-helper fat32$c
                           d-e-list entry-limit)))
  :hints
  (("goal"
    :in-theory (e/d (d-e-cc)
                    (lofat-to-hifat-helper-of-update-dir-contents))
    :use (:instance lofat-to-hifat-helper-of-update-dir-contents
                    (first-cluster (d-e-first-cluster root-d-e))))))

;; Slightly better than lofat-to-hifat-helper-of-clear-cc
(defthm
  lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-3
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (not (d-e-directory-p d-e))
        (<= *ms-first-data-cluster*
            (d-e-first-cluster d-e))
        (< (d-e-first-cluster d-e)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c)))
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0)
        (not-intersectp-list
         (mv-nth 0
                 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c
                                        d-e-list entry-limit))))
   (equal (lofat-to-hifat-helper
           (mv-nth 0
                   (clear-cc fat32$c
                             (d-e-first-cluster d-e)
                             (d-e-file-size d-e)))
           d-e-list entry-limit)
          (lofat-to-hifat-helper fat32$c
                                 d-e-list entry-limit)))
  :hints
  (("goal"
    :in-theory (e/d (d-e-cc)
                    (lofat-to-hifat-helper-of-clear-cc))
    :use (:instance lofat-to-hifat-helper-of-clear-cc
                    (masked-current-cluster (d-e-first-cluster d-e))
                    (length (d-e-file-size d-e))))))

;; Slightly better than lofat-to-hifat-helper-of-clear-cc
(defthm
  lofat-to-hifat-helper-of-lofat-remove-file-disjoint-lemma-4
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (<= *ms-first-data-cluster*
            (d-e-first-cluster d-e))
        (< (d-e-first-cluster d-e)
           (+ *ms-first-data-cluster*
              (count-of-clusters fat32$c)))
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0)
        (not-intersectp-list
         (mv-nth 0
                 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c
                                        d-e-list entry-limit))))
   (equal (lofat-to-hifat-helper
           (mv-nth 0
                   (clear-cc fat32$c
                             (d-e-first-cluster d-e)
                             *ms-max-dir-size*))
           d-e-list entry-limit)
          (lofat-to-hifat-helper fat32$c
                                 d-e-list entry-limit)))
  :hints
  (("goal"
    :in-theory (e/d (d-e-cc)
                    (lofat-to-hifat-helper-of-clear-cc))
    :use (:instance lofat-to-hifat-helper-of-clear-cc
                    (masked-current-cluster (d-e-first-cluster d-e))
                    (length *ms-max-dir-size*)))))

(defthm
  no-duplicatesp-of-fat32-build-index-list-of-effective-fat-of-update-dir-contents
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-masked-entry-p first-cluster)
    (stringp dir-contents)
    (< 0 (len (explode dir-contents)))
    (<= (len (explode dir-contents))
        *ms-max-dir-size*)
    (equal
     (mv-nth 1
             (get-cc-contents fat32$c
                              first-cluster *ms-max-dir-size*))
     0)
    (equal (mv-nth 1
                   (update-dir-contents fat32$c
                                        first-cluster dir-contents))
           0))
   (no-duplicatesp-equal
    (mv-nth
     0
     (fat32-build-index-list
      (effective-fat
       (mv-nth 0
               (update-dir-contents fat32$c
                                    first-cluster dir-contents)))
      first-cluster *ms-max-dir-size*
      (cluster-size fat32$c)))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (update-dir-contents)
     ((:rewrite nth-of-set-indices-in-fa-table-when-member)))
    :expand
    ((fat32-build-index-list (effective-fat fat32$c)
                             first-cluster *ms-max-dir-size*
                             (cluster-size fat32$c))
     (get-cc-contents fat32$c first-cluster 2097152))
    :use
    ((:instance
      (:rewrite nth-of-set-indices-in-fa-table-when-member)
      (val 0)
      (index-list
       (cons
        first-cluster
        (mv-nth 0
                (fat32-build-index-list
                 (effective-fat fat32$c)
                 (fat32-entry-mask (fati first-cluster fat32$c))
                 (+ 2097152
                    (- (cluster-size fat32$c)))
                 (cluster-size fat32$c)))))
      (fa-table (effective-fat fat32$c))
      (n first-cluster))))))

(defthm
  no-duplicatesp-of-d-e-cc-of-update-dir-contents-coincident
  (implies
   (and
    (lofat-fs-p fat32$c)
    (fat32-masked-entry-p first-cluster)
    (< 0 (len (explode dir-contents)))
    (<= (len (explode dir-contents))
        *ms-max-dir-size*)
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0)
    (equal (mv-nth 1
                   (update-dir-contents fat32$c first-cluster dir-contents))
           0)
    (equal (d-e-first-cluster d-e)
           first-cluster)
    (d-e-directory-p d-e))
   (no-duplicatesp-equal
    (mv-nth
     0
     (d-e-cc (mv-nth 0
                     (update-dir-contents fat32$c first-cluster dir-contents))
             d-e))))
  :hints
  (("goal"
    :in-theory (e/d (d-e-cc d-e-cc-contents)
                    (no-duplicatesp-of-fat32-build-index-list-of-effective-fat-of-update-dir-contents))
    :use
    no-duplicatesp-of-fat32-build-index-list-of-effective-fat-of-update-dir-contents)))

(defthm
  get-cc-of-update-dir-contents-coincident-lemma-1
  (implies
   (not (equal (mv-nth 1
                       (clear-cc fat32$c first-cluster 2097152))
               0))
   (equal
    (fat32-build-index-list
     (effective-fat (mv-nth 0
                            (clear-cc fat32$c first-cluster 2097152)))
     first-cluster
     2097152 (cluster-size fat32$c))
    (fat32-build-index-list (effective-fat fat32$c)
                            first-cluster
                            2097152 (cluster-size fat32$c))))
  :hints (("goal" :in-theory (enable clear-cc)
           :do-not-induct t)))

(defthmd
  get-cc-of-update-dir-contents-coincident-lemma-11
  (equal (fat32-build-index-list fa-table masked-current-cluster
                                 length cluster-size)
         (mv (mv-nth 0
                     (fat32-build-index-list fa-table masked-current-cluster
                                             length cluster-size))
             (mv-nth 1
                     (fat32-build-index-list fa-table masked-current-cluster
                                             length cluster-size))))
  :hints (("goal" :in-theory (enable fat32-build-index-list))))

(defthm
  get-cc-of-update-dir-contents-coincident-lemma-12
  (implies
   (and (equal (mv-nth 1
                       (get-cc-contents fat32$c first-cluster 2097152))
               0)
        (<= 2 first-cluster))
   (equal
    (cons (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32$c)
                                          first-cluster
                                          2097152 (cluster-size fat32$c)))
          '(0))
    (fat32-build-index-list (effective-fat fat32$c)
                            first-cluster
                            2097152 (cluster-size fat32$c))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance (:rewrite get-cc-of-update-dir-contents-coincident-lemma-11)
               (cluster-size (cluster-size fat32$c))
               (length 2097152)
               (masked-current-cluster first-cluster)
               (fa-table (effective-fat fat32$c))))))

(defthm
  get-cc-of-update-dir-contents-coincident-lemma-8
  (<
   (binary-*
    (cluster-size fat32$c)
    (len
     (cdr (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32$c)
                                          first-cluster
                                          2097152 (cluster-size fat32$c))))))
   2097152)
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable (:linear len-of-fat32-build-index-list-1 . 3))
    :use (:instance (:linear len-of-fat32-build-index-list-1 . 3)
                    (length 2097152)
                    (masked-current-cluster first-cluster)
                    (fa-table (effective-fat fat32$c))
                    (cluster-size (cluster-size fat32$c)))))
  :rule-classes :linear)

;; This could be made more general, but it should at least be renamed...
(defthm
  lofat-place-file-correctness-lemma-123
  (implies
   (and (lofat-fs-p fat32$c)
        (equal (mv-nth 1
                       (fat32-build-index-list (effective-fat fat32$c)
                                               masked-current-cluster
                                               length (cluster-size fat32$c)))
               0))
   (<=
    (+ *ms-first-data-cluster* (count-of-clusters fat32$c))
    (fat32-entry-mask
     (fati
      (car
       (last (mv-nth 0
                     (fat32-build-index-list (effective-fat fat32$c)
                                             masked-current-cluster
                                             length (cluster-size fat32$c)))))
      fat32$c))))
  :hints
  (("goal" :induct (fat32-build-index-list (effective-fat fat32$c)
                                           masked-current-cluster
                                           length (cluster-size fat32$c))
    :in-theory (enable fat32-build-index-list nfix)))
  :rule-classes :linear)

(defthm
  get-cc-of-update-dir-contents-coincident-lemma-10
  (implies
   (and
    (lofat-fs-p fat32$c)
    (equal (mv-nth 1
                   (get-cc-contents fat32$c first-cluster 2097152))
           0)
    (<= 2 first-cluster)
    (consp
     (cdr (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32$c)
                                          first-cluster
                                          2097152 (cluster-size fat32$c))))))
   (<=
    (+ 2 (count-of-clusters fat32$c))
    (fat32-entry-mask
     (fati
      (car
       (last
        (cdr
         (mv-nth 0
                 (fat32-build-index-list (effective-fat fat32$c)
                                         first-cluster
                                         2097152 (cluster-size fat32$c))))))
      fat32$c))))
  :hints
  (("goal"
    :in-theory (disable (:linear lofat-place-file-correctness-lemma-123))
    :use (:instance (:linear lofat-place-file-correctness-lemma-123)
                    (length 2097152)
                    (masked-current-cluster first-cluster)
                    (fat32$c fat32$c))))
  :rule-classes :linear)

(encapsulate
  ()

  (local
   (defthm
     lemma-1
     (implies
      (and
       (equal (mv-nth 1
                      (clear-cc fat32$c first-cluster 2097152))
              0)
       (not
        (consp
         (cdr (mv-nth 0
                      (fat32-build-index-list (effective-fat fat32$c)
                                              first-cluster
                                              2097152 (cluster-size fat32$c))))))
       (not (fat32-is-eof (fat32-entry-mask (fati first-cluster fat32$c)))))
      (<= (+ 2 (count-of-clusters fat32$c))
          (fat32-entry-mask (fati first-cluster fat32$c))))
     :hints
     (("goal" :do-not-induct t
       :expand (fat32-build-index-list (effective-fat fat32$c)
                                       first-cluster
                                       2097152 (cluster-size fat32$c))
       :in-theory (enable fat32-build-index-list clear-cc)))
     :rule-classes :linear))

  (local
   (defthm
     lemma-2
     (implies
      (lofat-fs-p fat32$c)
      (equal
       (car (mv-nth 0
                    (fat32-build-index-list (effective-fat fat32$c)
                                            first-cluster
                                            2097152 (cluster-size fat32$c))))
       first-cluster))
     :hints
     (("goal" :in-theory
       (e/d (update-dir-contents
             place-contents
             (:linear hifat-to-lofat-inversion-lemma-16)
             (:rewrite fati-of-clear-cc . 1))
            nil)
       :expand (fat32-build-index-list (effective-fat fat32$c)
                                       first-cluster
                                       2097152 (cluster-size fat32$c))))))

  (defthm
    get-cc-of-update-dir-contents-coincident
    (implies
     (and
      (lofat-fs-p fat32$c)
      (fat32-masked-entry-p first-cluster)
      (stringp dir-contents)
      (< 0 (len (explode dir-contents)))
      (<= (len (explode dir-contents))
          *ms-max-dir-size*)
      (equal (mv-nth 1
                     (get-cc fat32$c
                             first-cluster *ms-max-dir-size*))
             0)
      (<= 2 first-cluster)
      (> (+ 2 (count-of-clusters fat32$c))
         first-cluster)
      (no-duplicatesp-equal (mv-nth 0
                                    (get-cc fat32$c
                                            first-cluster *ms-max-dir-size*))))
     (equal
      (get-cc (mv-nth 0
                      (update-dir-contents fat32$c first-cluster dir-contents))
              first-cluster *ms-max-dir-size*)
      (cond
       ((equal (mv-nth 1
                       (update-dir-contents fat32$c first-cluster dir-contents))
               0)
        (mv
         (cons
          first-cluster
          (find-n-free-clusters
           (update-nth
            first-cluster
            (fat32-update-lower-28 (fati first-cluster fat32$c)
                                   268435455)
            (effective-fat (mv-nth 0
                                   (clear-cc fat32$c first-cluster 2097152))))
           (+ -1
              (len (make-clusters dir-contents (cluster-size fat32$c))))))
         0))
       (t (get-cc fat32$c
                  first-cluster *ms-max-dir-size*)))))
    :hints
    (("goal" :in-theory
      (e/d (update-dir-contents
            place-contents
            (:linear hifat-to-lofat-inversion-lemma-16)
            (:rewrite fati-of-clear-cc . 1))
           nil)))))

;; This lemma might be creating unnecessary trouble when enabled...
(defthm
  d-e-cc-of-update-dir-contents-coincident
  (implies
   (and (equal (d-e-first-cluster d-e)
               first-cluster)
        (lofat-fs-p fat32$c)
        (fat32-masked-entry-p (d-e-first-cluster d-e))
        (stringp dir-contents)
        (< 0 (len (explode dir-contents)))
        (<= (len (explode dir-contents))
            2097152)
        (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c d-e)))
        (d-e-directory-p d-e)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0))
   (equal
    (d-e-cc (mv-nth 0
                    (update-dir-contents fat32$c first-cluster dir-contents))
            d-e)
    (if
        (equal (mv-nth 1
                       (update-dir-contents fat32$c (d-e-first-cluster d-e)
                                            dir-contents))
               0)
        (mv
         (cons
          (d-e-first-cluster d-e)
          (find-n-free-clusters
           (update-nth
            (d-e-first-cluster d-e)
            (fat32-update-lower-28 (fati (d-e-first-cluster d-e) fat32$c)
                                   268435455)
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth 0 (d-e-cc fat32$c d-e))
             (make-list-ac (len (mv-nth 0 (d-e-cc fat32$c d-e)))
                           0 nil)))
           (+ -1
              (len (make-clusters dir-contents (cluster-size fat32$c))))))
         0)
      (d-e-cc fat32$c d-e))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (d-e-cc d-e-cc-correctness-1)
                           (get-cc-alt))
           :use d-e-cc-correctness-1)))

(defthm
  lofat-remove-file-correctness-lemma-74
  (implies
   (and
    (useful-d-e-list-p d-e-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit))
           0)
    (<= *ms-first-data-cluster*
        (d-e-first-cluster (mv-nth 0
                                   (find-d-e d-e-list filename))))
    (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename)))
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32$c))))
   (not-intersectp-list
    (mv-nth
     '0
     (d-e-cc fat32$c
             (mv-nth '0
                     (find-d-e d-e-list filename))))
    (mv-nth '2
            (lofat-to-hifat-helper fat32$c
                                   (delete-d-e d-e-list filename)
                                   entry-limit))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper
      (:rewrite lofat-to-hifat-helper-correctness-4)
      not-intersectp-list)
     ((:rewrite not-intersectp-list-of-lofat-to-hifat-helper)
      (:definition free-index-listp)
      (:rewrite nth-of-effective-fat)))
    :induct t
    :expand (:free (y) (intersectp-equal nil y)))))

(defthm
  lofat-remove-file-correctness-lemma-4
  (implies
   (and (unsigned-byte-listp 8 dir-contents)
        (not (equal filename1 filename2))
        (not (equal (char-code (char filename2 0))
                    229)))
   (equal
    (len
     (explode
      (remove1-d-e
       (implode (nats=>chars (clear-d-e dir-contents filename1)))
       filename2)))
    (len (explode (remove1-d-e (nats=>string dir-contents)
                               filename2)))))
  :hints
  (("goal"
    :in-theory (e/d (remove1-d-e clear-d-e
                                 len-when-d-e-p
                                 nats=>string)
                    (nats=>chars-of-take))
    :induct (clear-d-e dir-contents filename1)
    :expand
    ((remove1-d-e
      (implode (append (nats=>chars (take 32 dir-contents))
                       (nats=>chars (clear-d-e (nthcdr 32 dir-contents)
                                               filename1))))
      filename2)
     (remove1-d-e (nats=>string dir-contents)
                  filename2)))))

(defthm lofat-remove-file-correctness-lemma-5
  (>= (len (explode (remove1-d-e dir-contents filename)))
      (- (len (explode dir-contents))
         *ms-d-e-length*))
  :hints (("goal" :in-theory (enable remove1-d-e)))
  :rule-classes :linear)

(defthm
  lofat-remove-file-correctness-1-lemma-31
  (implies
   (and (unsigned-byte-listp 8 dir-contents)
        (not (equal filename1 filename2))
        (not (equal filename1 filename3))
        (not (equal (char-code (char filename2 0))
                    229))
        (not (equal (char-code (char filename3 0))
                    229)))
   (equal
    (len
     (explode
      (remove1-d-e
       (remove1-d-e
        (implode (nats=>chars (clear-d-e dir-contents filename1)))
        filename2)
       filename3)))
    (len
     (explode (remove1-d-e (remove1-d-e (nats=>string dir-contents)
                                        filename2)
                           filename3)))))
  :hints
  (("goal"
    :in-theory (e/d (remove1-d-e clear-d-e
                                 len-when-d-e-p
                                 nats=>string)
                    (nats=>chars-of-take))
    :induct (clear-d-e dir-contents filename1)
    :expand
    ((remove1-d-e
      (implode (append (nats=>chars (take 32 dir-contents))
                       (nats=>chars (clear-d-e (nthcdr 32 dir-contents)
                                               filename1))))
      filename2)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (local
   (defthm
     lemma
     (implies (and (d-e-p d-e)
                   (< (nfix n) *ms-d-e-length*))
              (rationalp (nth n d-e)))
     :hints (("goal" :in-theory (enable d-e-p)))
     :rule-classes
     ((:rewrite
       :corollary (implies (and (d-e-p d-e)
                                (< (nfix n) *ms-d-e-length*))
                           (acl2-numberp (nth n d-e)))))))

  (make-event
   `(defthm
      lofat-remove-file-correctness-1-lemma-34
      (implies
       (and (equal (mod (len (explode dir-contents))
                        *ms-d-e-length*)
                   0)
            (equal (mod n *ms-d-e-length*) 0))
       (equal (remove1-d-e (implode (append (explode dir-contents)
                                            (make-list-ac n ,(code-char 0) nil)))
                           filename)
              (implode (append (explode (remove1-d-e dir-contents filename))
                               (make-list-ac n (code-char 0) nil)))))
      :hints (("goal" :in-theory (enable remove1-d-e)
               :induct (remove1-d-e dir-contents filename))
              ("subgoal *1/1" :expand (len (explode dir-contents))))))

  (make-event
   `(defthm
      lofat-remove-file-correctness-1-lemma-35
      (implies
       (and
        (equal (mod (length dir-contents)
                    *ms-d-e-length*)
               0)
        (equal (mod n *ms-d-e-length*) 0)
        (equal
         (len
          (explode (remove1-d-e (remove1-d-e dir-contents ".          ")
                                "..         ")))
         (+ -64 (len (explode dir-contents)))))
       (<=
        (len
         (explode
          (remove1-d-e
           (remove1-d-e (implode (append (explode dir-contents)
                                         (make-list-ac n ,(code-char 0) nil)))
                        ".          ")
           "..         ")))
        (+
         -32
         (len
          (explode (remove1-d-e (implode (append (explode dir-contents)
                                                 (make-list-ac n ,(code-char 0) nil)))
                                ".          "))))))
      :hints
      (("goal" :in-theory (enable remove1-d-e nfix)
        :induct (remove1-d-e dir-contents ".          "))
       ("subgoal *1/4.4''"
        :in-theory (disable lofat-remove-file-correctness-1-lemma-34)
        :use
        (:instance
         lofat-remove-file-correctness-1-lemma-34
         (filename *parent-dir-fat32-name*)
         (dir-contents
          (remove1-d-e (implode (nthcdr 32 (explode dir-contents)))
                       *current-dir-fat32-name*))))
       ("subgoal *1/3.2'"
        :in-theory (disable lofat-remove-file-correctness-1-lemma-34)
        :use
        (:instance (:rewrite lofat-remove-file-correctness-1-lemma-34)
                   (filename "..         ")
                   (n n)
                   (dir-contents (implode (nthcdr 32 (explode dir-contents)))))))
      :rule-classes :linear))

  (make-event
   `(defthm
      lofat-place-file-correctness-lemma-138
      (implies
       (and (equal (mod (len (explode (implode dir-contents)))
                        32)
                   0)
            (equal (mod n 32) 0))
       (equal
        (remove1-d-e (implode (append dir-contents (make-list-ac n ,(code-char 0) nil)))
                     filename)
        (implode (append (explode (remove1-d-e (implode dir-contents)
                                               filename))
                         (make-list-ac n ,(code-char 0) nil)))))
      :hints
      (("goal" :in-theory (disable lofat-remove-file-correctness-1-lemma-34)
        :use (:instance lofat-remove-file-correctness-1-lemma-34
                        (dir-contents (implode dir-contents)))))))

  (make-event
   `(defthm
      lofat-place-file-correctness-lemma-141
      (implies
       (and (stringp contents)
            (subdir-contents-p contents)
            (equal (mod (len (explode contents))
                        *ms-d-e-length*)
                   0)
            (equal (mod n *ms-d-e-length*) 0))
       (subdir-contents-p (implode (append (explode contents)
                                           (make-list-ac n ,(code-char 0) nil)))))
      :hints (("goal" :in-theory (enable subdir-contents-p nfix remove1-d-e)
               :induct (remove1-d-e contents *current-dir-fat32-name*))))))

(make-event
 `(defthm
    lofat-place-file-correctness-lemma-149
    (implies
     (and (subdir-contents-p (implode contents))
          (equal (mod (len (explode (implode contents)))
                      32)
                 0)
          (equal (mod n 32) 0))
     (subdir-contents-p (implode (append contents (make-list-ac n ,(code-char 0) nil)))))
    :hints (("goal" :in-theory (disable lofat-place-file-correctness-lemma-141)
             :use ((:instance lofat-place-file-correctness-lemma-141
                              (contents (implode contents))))))))

(make-event
 `(defthmd
    lofat-place-file-correctness-lemma-142
    (implies
     (and (unsigned-byte-listp 8 dir-contents)
          (subdir-contents-p (nats=>string dir-contents))
          (fat32-filename-p filename)
          (equal (mod n 32) 0)
          (equal (mod (length dir-contents) 32)
                 0))
     (subdir-contents-p
      (implode (append (nats=>chars (clear-d-e dir-contents filename))
                       (make-list-ac n ,(code-char 0) nil)))))
    :hints
    (("goal" :do-not-induct t
      :in-theory (e/d (subdir-contents-p nats=>string
                                         fat32-filename-p)
                      (lofat-remove-file-correctness-1-lemma-34
                       lofat-remove-file-correctness-1-lemma-35))
      :use ((:instance (:linear lofat-remove-file-correctness-1-lemma-35)
                       (dir-contents (implode (nats=>chars dir-contents))))
            (:instance (:rewrite lofat-remove-file-correctness-1-lemma-34)
                       (filename *current-dir-fat32-name*)
                       (dir-contents (implode (nats=>chars dir-contents)))))))))

(encapsulate
  ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                                hist pspv)))

  (defthm
    lofat-remove-file-correctness-1-lemma-40
    (implies
     (lofat-fs-p fat32$c)
     (integerp (binary-* '1/32
                         (cluster-size fat32$c))))
    :hints (("goal" :in-theory (disable lofat-fs-p-correctness-1)
             :use lofat-fs-p-correctness-1)))

  (defthm lofat-remove-file-correctness-1-lemma-41
    (implies
     (and (lofat-fs-p fat32$c)
          (d-e-directory-p d-e))
     (integerp
      (*
       1/32
       (len
        (explode
         (mv-nth
          0
          (d-e-cc-contents fat32$c d-e)))))))
    :hints (("goal" :in-theory
             (disable
              root-d-e-list-of-lofat-remove-file-coincident-lemma-2
              lofat-fs-p-correctness-1)
             :use (lofat-fs-p-correctness-1
                   (:instance
                    root-d-e-list-of-lofat-remove-file-coincident-lemma-2
                    (y 32)))) )))

(defund good-root-d-e-p (root-d-e fat32$c)
  (declare (xargs :stobjs fat32$c))
  (b*
      (((unless (and (lofat-fs-p fat32$c)
                     (d-e-p root-d-e)
                     (d-e-directory-p root-d-e)
                     (<= *ms-first-data-cluster* (d-e-first-cluster root-d-e))
                     (< (d-e-first-cluster root-d-e)
                        (+ *ms-first-data-cluster* (count-of-clusters fat32$c)))))
        nil)
       ((mv & error-code) (d-e-cc-contents fat32$c
                                           root-d-e))
       ((mv cc &)
        (d-e-cc fat32$c root-d-e)))
    (and (equal error-code 0)
         (no-duplicatesp-equal cc))))

(defthm good-root-d-e-p-of-pseudo-root-d-e
  (implies
   (and
    (lofat-fs-p fat32$c)
    (equal
     (mv-nth
      1
      (d-e-cc-contents fat32$c
                       (pseudo-root-d-e fat32$c)))
     0)
    (no-duplicatesp-equal
     (mv-nth 0
             (d-e-cc fat32$c
                     (pseudo-root-d-e fat32$c)))))
   (good-root-d-e-p (pseudo-root-d-e fat32$c)
                    fat32$c))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (good-root-d-e-p)))))

(defun
    insert-d-e-helper
    (dir-contents ac parent-d-e current-d-e)
  (declare
   (xargs
    :guard (and (stringp dir-contents)
                (d-e-list-p ac))
    :measure (length dir-contents)
    :guard-hints (("goal" :in-theory (enable d-e-p)))))
  (b*
      (((when (< (length dir-contents)
                 *ms-d-e-length*))
        (mv (revappend ac nil)
            parent-d-e current-d-e))
       (d-e
        (mbe
         :exec
         (string=>nats (subseq dir-contents 0 *ms-d-e-length*))
         :logic (d-e-fix
                 (chars=>nats (take *ms-d-e-length*
                                    (explode dir-contents))))))
       ((when (equal (char (d-e-filename d-e) 0)
                     (code-char 0)))
        (mv (revappend ac nil)
            parent-d-e current-d-e))
       ((when (equal (d-e-filename d-e)
                     *parent-dir-fat32-name*))
        (insert-d-e-helper
         (subseq dir-contents *ms-d-e-length* nil)
         ac d-e current-d-e))
       ((when (equal (d-e-filename d-e)
                     *current-dir-fat32-name*))
        (insert-d-e-helper
         (subseq dir-contents *ms-d-e-length* nil)
         ac parent-d-e d-e))
       ((when (useless-d-e-p d-e))
        (insert-d-e-helper
         (subseq dir-contents *ms-d-e-length* nil)
         ac parent-d-e current-d-e)))
    (insert-d-e-helper
     (subseq dir-contents *ms-d-e-length* nil)
     (list* d-e ac)
     parent-d-e current-d-e)))

(defthm
  insert-d-e-helper-correctness-1
  (equal (mv-nth 0
                 (insert-d-e-helper
                  dir-contents
                  ac parent-d-e current-d-e))
         (revappend ac (make-d-e-list dir-contents)))
  :hints
  (("goal"
    :in-theory (enable make-d-e-list useless-d-e-p))))

(defthm
  d-e-p-of-insert-d-e-helper
  (implies
   (and (d-e-p parent-d-e)
        (d-e-p current-d-e))
   (and (d-e-p (mv-nth 1
                       (insert-d-e-helper dir-contents
                                          ac parent-d-e current-d-e)))
        (d-e-p (mv-nth 2
                       (insert-d-e-helper dir-contents
                                          ac parent-d-e current-d-e))))))

(defund
  insert-d-e (dir-contents d-e)
  (declare
   (xargs :guard (and (d-e-p d-e)
                      (unsigned-byte-listp 8 dir-contents))
          :guard-hints (("goal" :in-theory (enable d-e-p)))))
  (b*
      (((mv d-e-list parent-d-e current-d-e)
        (insert-d-e-helper (nats=>string dir-contents) nil nil nil)))
    (append
     (d-e-set-filename (d-e-fix current-d-e) *current-dir-fat32-name*)
     (d-e-set-filename (d-e-fix parent-d-e) *parent-dir-fat32-name*)
     (flatten (place-d-e d-e-list d-e)))))

(defthm
  unsigned-byte-listp-of-insert-d-e
  (implies
   (unsigned-byte-listp 8 dir-contents)
   (unsigned-byte-listp 8
                        (insert-d-e dir-contents d-e)))
  :hints (("goal" :in-theory (enable insert-d-e))))

(defthmd insert-d-e-of-d-e-fix
  (equal (insert-d-e dir-contents (d-e-fix d-e))
         (insert-d-e dir-contents d-e))
  :hints (("goal" :in-theory (enable insert-d-e))))

(defcong
  d-e-equiv equal
  (insert-d-e dir-contents d-e)
  2
  :hints
  (("goal"
    :use ((:rewrite insert-d-e-of-d-e-fix)
          (:instance (:rewrite insert-d-e-of-d-e-fix)
                     (d-e d-e-equiv))))))

(defthm
  len-of-insert-d-e
  (equal
   (len (insert-d-e dir-contents d-e))
   (* 32
      (+ 2
         (len (place-d-e (make-d-e-list (nats=>string dir-contents))
                         d-e)))))
  :hints (("goal" :in-theory (e/d (insert-d-e len-when-d-e-p)))))

(encapsulate
  ()

  (local
   (defthm lemma
     (implies (< (nfix n) *ms-d-e-length*)
              (natp (nth n (d-e-fix d-e))))
     :hints (("goal" :in-theory (disable (:linear nth-when-d-e-p))
              :use (:instance (:linear nth-when-d-e-p)
                              (d-e (d-e-fix d-e)))))
     :rule-classes :type-prescription))

  (defthm
    make-d-e-list-of-insert-d-e-lemma-1
    (implies
     (and (not (equal (nth 0 (explode (d-e-filename d-e)))
                      (code-char 0)))
          (not (useless-d-e-p (d-e-fix d-e))))
     (equal (make-d-e-list (implode (nats=>chars (d-e-fix d-e))))
            (list (d-e-fix d-e))))
    :hints
    (("goal"
      :in-theory (enable make-d-e-list
                         insert-d-e string=>nats
                         nats=>string
                         len-when-d-e-p)
      :do-not-induct t
      :expand
      (make-d-e-list (implode (nats=>chars (d-e-fix d-e)))))))

  ;; Hypotheses are minimal
  (defthm
    make-d-e-list-of-insert-d-e
    (implies
     (and (not (equal (nth 0 (explode (d-e-filename d-e)))
                      (code-char 0)))
          (not (useless-d-e-p (d-e-fix d-e))))
     (equal (make-d-e-list
             (nats=>string (insert-d-e (string=>nats dir-contents)
                                       d-e)))
            (place-d-e (make-d-e-list dir-contents)
                       d-e)))
    :hints (("goal" :in-theory (enable make-d-e-list insert-d-e
                                       string=>nats nats=>string)))))

(defthm stringp-of-insert-d-e
  (implies (unsigned-byte-listp 8 dir-contents)
           (unsigned-byte-listp 8
                                (insert-d-e dir-contents d-e)))
  :hints (("goal" :in-theory (enable insert-d-e))))

(defthm lofat-place-file-correctness-lemma-1
  (implies (good-root-d-e-p root-d-e fat32$c)
           (and
            (d-e-p root-d-e)
            (d-e-directory-p root-d-e)
            (lofat-fs-p fat32$c)
            (>= (d-e-first-cluster root-d-e) *ms-first-data-cluster*)
            (< (d-e-first-cluster root-d-e)
               (binary-+ '2
                         (count-of-clusters fat32$c)))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable good-root-d-e-p)))
  :rule-classes :forward-chaining)

(defthm
  lofat-place-file-correctness-lemma-5
  (implies
   (good-root-d-e-p root-d-e fat32$c)
   (and
    (equal
     (mv-nth 1
             (d-e-cc-contents fat32$c root-d-e))
     0)
    (no-duplicatesp-equal
     (mv-nth 0
             (d-e-cc fat32$c root-d-e)))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable good-root-d-e-p))))

(defthm
  lofat-remove-file-correctness-lemma-11
  (implies
   (and
    (<= 2 (d-e-first-cluster d-e))
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c d-e))
           0))
   (member-equal (d-e-first-cluster d-e)
                 (mv-nth 0
                         (d-e-cc fat32$c d-e))))
  :hints (("goal" :in-theory (enable d-e-cc
                                     d-e-cc-contents))))

(defthm
  lofat-remove-file-correctness-lemma-12
  (implies
   (and (d-e-p d-e)
        (< (d-e-first-cluster d-e)
           (len (effective-fat fat32$c))))
   (bounded-nat-listp (mv-nth '0
                              (d-e-cc fat32$c d-e))
                      (binary-+ '2
                                (count-of-clusters fat32$c))))
  :hints (("goal" :in-theory (enable d-e-cc nfix))))

(defthm
  lofat-remove-file-correctness-lemma-13
  (implies
   (and
    (lofat-fs-p fat32$c)
    (d-e-p d-e)
    (d-e-directory-p d-e)
    (<= *ms-first-data-cluster*
        (d-e-first-cluster d-e))
    (> (+ *ms-first-data-cluster*
          (count-of-clusters fat32$c))
       (d-e-first-cluster d-e))
    (stringp dir-contents)
    (equal (mv-nth 1
                   (d-e-cc-contents fat32$c d-e))
           0)
    (no-duplicatesp-equal
     (mv-nth 0
             (d-e-cc fat32$c d-e))))
   (equal
    (mv-nth 1
            (update-dir-contents fat32$c
                                 (d-e-first-cluster d-e)
                                 dir-contents))
    (if
        (and (< 0 (len (explode dir-contents)))
             (< (+ (count-free-clusters (effective-fat fat32$c))
                   (len (mv-nth 0
                                (d-e-cc fat32$c d-e))))
                (len (make-clusters dir-contents
                                    (cluster-size fat32$c)))))
        *enospc* 0)))
  :hints (("goal" :in-theory (enable update-dir-contents
                                     d-e-cc-contents
                                     clear-cc-correctness-1))))

(defthm lofat-place-file-correctness-lemma-145
  (implies (lofat-regular-file-p file)
           (> (ash 1 32)
              (len (explode (lofat-file->contents file)))))
  :hints (("goal" :in-theory (enable lofat-regular-file-p
                                     lofat-file->contents)))
  :rule-classes :linear)

(defthm
  lofat-place-file-correctness-lemma-77
  (equal (hifat-equiv (cons (cons name (m1-file d-e1 fs))
                            y)
                      (cons (cons name (m1-file d-e2 fs))
                            y))
         t)
  :hints (("goal" :in-theory (enable hifat-equiv
                                     hifat-subsetp hifat-file-alist-fix
                                     hifat-no-dups-p m1-file-contents-fix
                                     m1-file-contents-p))))

;; Slightly better version of non-free-index-listp-correctness-2 for
;; clusterchains.
(defthm
  lofat-place-file-correctness-lemma-18
  (implies
   (and (<= *ms-first-data-cluster*
            (d-e-first-cluster d-e))
        (equal (mv-nth 1
                       (d-e-cc fat32$c d-e))
               0)
        (equal (fat32-entry-mask (nth key (effective-fat fat32$c)))
               0))
   (not
    (member-equal key
                  (mv-nth 0
                          (d-e-cc fat32$c d-e)))))
  :hints
  (("goal"
    :in-theory (disable non-free-index-listp-correctness-2)
    :use
    (:instance non-free-index-listp-correctness-2
               (x (mv-nth 0
                          (d-e-cc fat32$c d-e)))
               (fa-table (effective-fat fat32$c))))))

(defund
  make-empty-subdir-contents
  (current-dir-first-cluster parent-dir-first-cluster)
  (declare (xargs :guard (and
                          (fat32-masked-entry-p current-dir-first-cluster)
                          (fat32-masked-entry-p parent-dir-first-cluster))))
  (nats=>string
   (append (d-e-set-first-cluster-file-size
            (d-e-set-filename (d-e-fix nil)
                              *current-dir-fat32-name*)
            current-dir-first-cluster 0)
           (d-e-set-first-cluster-file-size
            (d-e-set-filename (d-e-fix nil)
                              *parent-dir-fat32-name*)
            parent-dir-first-cluster 0))))

(defthm
  length-of-make-empty-subdir-contents
  (equal (len (explode (make-empty-subdir-contents current-dir-first-cluster
                                                   parent-dir-first-cluster)))
         64)
  :hints (("goal" :do-not-induct t
           :in-theory (enable make-empty-subdir-contents
                              len-when-d-e-p))))

(defthm
  make-d-e-list-of-make-empty-subdir-contents
  (equal
   (make-d-e-list (make-empty-subdir-contents current-dir-first-cluster
                                              parent-dir-first-cluster))
   nil)
  :hints (("goal" :do-not-induct t
           :in-theory (enable make-empty-subdir-contents
                              make-d-e-list len-when-d-e-p))))

(defthm
  lofat-place-file-correctness-lemma-21
  (implies
   (good-root-d-e-p root-d-e fat32$c)
   (>=
    2097152
    (*
     (cluster-size fat32$c)
     (len
      (make-clusters
       (make-empty-subdir-contents i (d-e-first-cluster root-d-e))
       (cluster-size fat32$c))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (enable make-empty-subdir-contents
                       make-clusters len-when-d-e-p
                       nthcdr-when->=-n-len-l)
    :expand
    (make-clusters
     (nats=>string (append (d-e-set-first-cluster-file-size
                            '(46 32 32 32 32 32 32 32 32 32 32 0
                                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                            i 0)
                           (d-e-set-first-cluster-file-size
                            '(46 46 32 32 32 32 32 32 32 32 32 0
                                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                            (d-e-first-cluster root-d-e)
                            0)))
     (cluster-size fat32$c))))
  :rule-classes :linear)

(defthm
  lofat-place-file-correctness-lemma-22
  (implies
   (and (fat32-masked-entry-p i)
        (d-e-p root-d-e)
        (not (stringp y)))
   (subdir-contents-p
    (implode
     (append
      (explode (make-empty-subdir-contents i (d-e-first-cluster root-d-e)))
      y))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable subdir-contents-p
                              make-empty-subdir-contents
                              remove1-d-e))))

(encapsulate
  ()

  (local
   (defthm lemma
     (implies
      (natp masked-current-cluster)
      (nat-listp (mv-nth 0
                         (fat32-build-index-list fa-table masked-current-cluster
                                                 length cluster-size))))
     :hints (("goal" :in-theory (enable fat32-build-index-list nat-listp)))))

  (defthm
    lofat-place-file-correctness-lemma-33
    (implies
     (and
      (not
       (intersectp-equal
        (mv-nth '0
                (fat32-build-index-list (effective-fat fat32$c)
                                        masked-current-cluster
                                        length (cluster-size fat32$c)))
        (mv-nth '0
                (d-e-cc fat32$c d-e))))
      (lofat-fs-p fat32$c)
      (natp masked-current-cluster))
     (equal (d-e-cc-contents
             (mv-nth 0
                     (clear-cc fat32$c
                               masked-current-cluster length))
             d-e)
            (d-e-cc-contents fat32$c d-e)))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (d-e-cc d-e-cc-contents
                              get-cc-contents
                              clear-cc)
                      (d-e-cc-contents-of-clear-cc))))))

(defthm lofat-place-file-correctness-lemma-34
  (equal (clear-cc fat32$c first-cluster 0)
         (mv fat32$c (- *eio*)))
  :hints (("goal" :in-theory (enable clear-cc
                                     fat32-build-index-list))))

;; I don't like this...
(defthm
  lofat-place-file-correctness-1-lemma-25
  (implies (equal (mv-nth 1
                          (d-e-cc fat32$c d-e))
                  0)
           (not
            (<
             (binary-+
              (count-free-clusters (effective-fat fat32$c))
              (len (mv-nth '0
                           (d-e-cc fat32$c d-e))))
             '1)))
  :hints
  (("goal"
    :in-theory (enable d-e-cc
                       fat32-build-index-list)
    :expand ((fat32-build-index-list (effective-fat fat32$c)
                                     (d-e-first-cluster d-e)
                                     (d-e-file-size d-e)
                                     (cluster-size fat32$c))
             (fat32-build-index-list (effective-fat fat32$c)
                                     (d-e-first-cluster d-e)
                                     2097152
                                     (cluster-size fat32$c)))))
  :rule-classes (:rewrite :linear))

(defthm
  d-e-cc-contents-of-lofat-place-file-coincident-lemma-5
  (implies
   (and (<= 2 (d-e-first-cluster d-e))
        (equal (mv-nth 1
                       (d-e-cc fat32$c d-e))
               0)
        (no-duplicatesp-equal
         (mv-nth 0
                 (d-e-cc fat32$c d-e))))
   (equal
    (count-free-clusters
     (set-indices-in-fa-table
      (effective-fat fat32$c)
      (mv-nth 0
              (d-e-cc fat32$c d-e))
      (make-list-ac
       (len (mv-nth 0
                    (d-e-cc fat32$c d-e)))
       0 nil)))
    (+ (count-free-clusters (effective-fat fat32$c))
       (len (mv-nth 0
                    (d-e-cc fat32$c d-e)))))))

(defthm
  lofat-place-file-correctness-lemma-87
  (implies
   (and
    (lofat-fs-p fat32$c)
    (not
     (member-equal
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32$c)
         (mv-nth 0
                 (d-e-cc fat32$c
                         (mv-nth 0 (find-d-e d-e-list filename))))
         (make-list-ac
          (len (mv-nth 0
                       (d-e-cc fat32$c
                               (mv-nth 0 (find-d-e d-e-list filename)))))
          0 nil))
        1))
      (mv-nth 0
              (d-e-cc fat32$c
                      (mv-nth 0 (find-d-e d-e-list filename))))))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
           0)
    (<= 2
        (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename))))
    (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename)))
       (+ 2 (count-of-clusters fat32$c)))
    (useful-d-e-list-p d-e-list))
   (equal
    (fat32-entry-mask
     (fati
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32$c)
         (mv-nth 0
                 (d-e-cc fat32$c
                         (mv-nth 0 (find-d-e d-e-list filename))))
         (make-list-ac
          (len (mv-nth 0
                       (d-e-cc fat32$c
                               (mv-nth 0 (find-d-e d-e-list filename)))))
          0 nil))
        1))
      fat32$c))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite nth-of-set-indices-in-fa-table-when-member)
                        (:rewrite find-n-free-clusters-correctness-5))
    :use
    ((:instance
      (:rewrite nth-of-set-indices-in-fa-table-when-member)
      (val 0)
      (index-list (mv-nth 0
                          (d-e-cc fat32$c
                                  (mv-nth 0 (find-d-e d-e-list filename)))))
      (fa-table (effective-fat fat32$c))
      (n
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth 0
                  (d-e-cc fat32$c
                          (mv-nth 0 (find-d-e d-e-list filename))))
          (make-list-ac
           (len (mv-nth 0
                        (d-e-cc fat32$c
                                (mv-nth 0 (find-d-e d-e-list filename)))))
           0 nil))
         1))))
     (:instance
      (:rewrite find-n-free-clusters-correctness-5)
      (n1 1)
      (fa-table
       (set-indices-in-fa-table
        (effective-fat fat32$c)
        (mv-nth 0
                (d-e-cc fat32$c
                        (mv-nth 0 (find-d-e d-e-list filename))))
        (make-list-ac
         (len (mv-nth 0
                      (d-e-cc fat32$c
                              (mv-nth 0 (find-d-e d-e-list filename)))))
         0 nil)))
      (n2 0))))))

(defthm
  lofat-place-file-correctness-lemma-42
  (implies
   (and (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               0)
        (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c d-e)))
        (not-intersectp-list
         (mv-nth 0 (d-e-cc fat32$c d-e))
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))
   (not-intersectp-list
    (list (nth 0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth 0 (d-e-cc fat32$c d-e))
                 (make-list-ac (len (mv-nth 0 (d-e-cc fat32$c d-e)))
                               0 nil))
                1)))
    (mv-nth 2
            (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    ((:instance
      (:rewrite non-free-index-list-listp-correctness-1)
      (l (mv-nth 2
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
      (index-list
       (list
        (nth 0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth 0 (d-e-cc fat32$c d-e))
               (make-list-ac (len (mv-nth 0 (d-e-cc fat32$c d-e)))
                             0 nil))
              1))))
      (fa-table (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth 0 (d-e-cc fat32$c d-e))
                 (make-list-ac (len (mv-nth 0 (d-e-cc fat32$c d-e)))
                               0 nil))))))))

(defthm
  d-e-cc-contents-of-lofat-place-file-coincident-lemma-3
  (and
   (implies
    (and (d-e-directory-p d-e)
         (<= 2 (d-e-first-cluster d-e)))
    (equal (mv-nth 1
                   (clear-cc fat32$c
                             (d-e-first-cluster d-e)
                             *ms-max-dir-size*))
           (mv-nth 1
                   (d-e-cc-contents fat32$c d-e))))
   (implies
    (and (not (d-e-directory-p d-e))
         (<= 2 (d-e-first-cluster d-e)))
    (equal (mv-nth 1
                   (clear-cc fat32$c
                             (d-e-first-cluster d-e)
                             (d-e-file-size d-e)))
           (mv-nth 1
                   (d-e-cc-contents fat32$c d-e)))))
  :hints (("goal" :in-theory (enable d-e-cc-contents
                                     clear-cc-correctness-1))))

(defthm
  d-e-cc-contents-of-lofat-place-file-coincident-lemma-6
  t
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (<= 2 (d-e-first-cluster d-e))
          (lofat-fs-p fat32$c)
          (d-e-directory-p d-e))
     (equal
      (effective-fat (mv-nth 0
                             (clear-cc fat32$c
                                       (d-e-first-cluster d-e)
                                       *ms-max-dir-size*)))
      (if
          (equal (mv-nth 1
                         (clear-cc fat32$c
                                   (d-e-first-cluster d-e)
                                   *ms-max-dir-size*))
                 0)
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth 0
                   (d-e-cc fat32$c d-e))
           (make-list-ac
            (len (mv-nth 0
                         (d-e-cc fat32$c d-e)))
            0 nil))
        (effective-fat fat32$c))))
    :hints (("goal" :in-theory (enable d-e-cc
                                       d-e-cc-contents))))
   (:rewrite
    :corollary
    (implies
     (and (<= 2 (d-e-first-cluster d-e))
          (lofat-fs-p fat32$c)
          (not (d-e-directory-p d-e)))
     (equal
      (effective-fat (mv-nth 0
                             (clear-cc fat32$c
                                       (d-e-first-cluster d-e)
                                       (d-e-file-size d-e))))
      (if
          (equal (mv-nth 1
                         (clear-cc fat32$c
                                   (d-e-first-cluster d-e)
                                   (d-e-file-size d-e)))
                 0)
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth 0
                   (d-e-cc fat32$c d-e))
           (make-list-ac
            (len (mv-nth 0
                         (d-e-cc fat32$c d-e)))
            0 nil))
        (effective-fat fat32$c))))
    :hints (("goal" :in-theory (enable d-e-cc
                                       d-e-cc-contents))))))

(defthm
  lofat-place-file-guard-lemma-1
  (implies (lofat-regular-file-p file)
           (unsigned-byte-p
            32
            (len (explode (lofat-file->contents file)))))
  :hints (("goal" :in-theory (enable lofat-regular-file-p))))

(defthm
  lofat-place-file-correctness-lemma-103
  (equal (hifat-equiv (cons (cons name
                                  (m1-file-hifat-file-alist-fix d-e1 fs))
                            y)
                      (cons (cons name
                                  (m1-file-hifat-file-alist-fix d-e2 fs))
                            y))
         t)
  :hints
  (("goal" :in-theory (e/d (m1-file-hifat-file-alist-fix)
                           (m1-file-hifat-file-alist-fix-normalisation)))))

(local
 (defthm
   lofat-place-file-correctness-lemma-90
   (implies (fat32-filename-p name)
            (not (useless-d-e-p (make-d-e-with-filename name))))
   :hints (("goal" :do-not-induct t
            :in-theory (enable make-d-e-with-filename)))))

(defthm
  lofat-place-file-correctness-lemma-50
  (implies (and (non-free-index-list-listp l fa-table)
                (equal (fat32-entry-mask (nth key fa-table))
                       0))
           (non-free-index-list-listp l (update-nth key val fa-table)))
  :hints (("Goal" :in-theory (enable nfix non-free-index-listp))))

(defthm
  lofat-place-file-correctness-lemma-58
  (implies
   (and
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit1))
     0)
    (>=
     (nfix entry-limit2)
     (mv-nth 1
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit1))))
   (equal
    (mv-nth 3
            (lofat-to-hifat-helper fat32$c
                                   d-e-list entry-limit2))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable lofat-to-hifat-helper-correctness-4)
    :use lofat-to-hifat-helper-correctness-4)))

(defthm
  lofat-place-file-correctness-lemma-56
  (implies
   (and (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
               0)
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit1)))
        (>= (nfix entry-limit2)
            (mv-nth 1
                    (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
   (not-intersectp-list
    x
    (mv-nth 2
            (lofat-to-hifat-helper fat32$c d-e-list entry-limit2))))
  :hints (("goal" :do-not-induct t
           :use lofat-to-hifat-helper-correctness-4)))

(local
 (defthm
   lofat-place-file-correctness-lemma-36
   (implies
    (and (equal (mv-nth 3
                        (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
                0)
         (<= (mv-nth 1
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
             (nfix entry-limit2)))
    (and
     (equal
      (hifat-equiv
       (cons
        (cons
         name
         (m1-file-hifat-file-alist-fix
          d-e1
          x))
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit1)))
       (cons
        (cons
         name
         (m1-file-hifat-file-alist-fix
          d-e2
          x))
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit2))))
      t)
     (equal
      (hifat-equiv
       (cons
        (cons
         name
         (m1-file-hifat-file-alist-fix
          d-e2
          x))
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit2)))
       (cons
        (cons
         name
         (m1-file-hifat-file-alist-fix
          d-e1
          x))
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
      t)))
   :hints (("goal" :do-not-induct t
            :use lofat-to-hifat-helper-correctness-4))))

(defthm
  lofat-place-file-correctness-lemma-188
  (implies
   (and (equal (fat32-entry-mask (fati i fat32$c))
               0)
        (fat32-masked-entry-p i)
        (lofat-fs-p fat32$c)
        (<= (len (make-clusters (lofat-file->contents file)
                                (cluster-size fat32$c)))
            (count-free-clusters (effective-fat fat32$c)))
        (< 0
           (len (explode (lofat-file->contents file))))
        (< i (+ 2 (count-of-clusters fat32$c)))
        (<= 2 i))
   (equal
    (mv-nth
     '2
     (place-contents (update-fati i
                                  (fat32-update-lower-28 (fati i fat32$c)
                                                         '268435455)
                                  fat32$c)
                     d-e (lofat-file->contents$inline file)
                     (len (explode$inline (lofat-file->contents$inline file)))
                     i))
    '0))
  :hints (("goal" :do-not-induct t)))

(defthm
  lofat-place-file-correctness-lemma-121
  (implies
   (and
    (not (member-intersectp-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
          y1))
    (subsetp-equal y2 (cons nil y1))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
           0)
    (>= (nfix entry-limit2)
        (mv-nth 1
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
   (and
    (not (member-intersectp-equal
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c d-e-list entry-limit2))
          y2))
    (not (member-intersectp-equal
          y2
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c d-e-list entry-limit2))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable not-intersectp-list-of-set-difference$-lemma-3)
    :use
    ((:instance
      not-intersectp-list-of-set-difference$-lemma-3
      (x (mv-nth 2
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit2))))
     lofat-to-hifat-helper-correctness-4)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (not (member-intersectp-equal
            y1
            (mv-nth 2
                    (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
      (subsetp-equal y2 (cons nil y1))
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
             0)
      (>= (nfix entry-limit2)
          (mv-nth 1
                  (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
     (and
      (not (member-intersectp-equal
            (mv-nth 2
                    (lofat-to-hifat-helper fat32$c d-e-list entry-limit2))
            y2))
      (not (member-intersectp-equal
            y2
            (mv-nth 2
                    (lofat-to-hifat-helper fat32$c d-e-list entry-limit2)))))))))

(defthm
  lofat-place-file-guard-lemma-2
  (implies (and (lofat-file-p file)
                (not (lofat-directory-file-p file)))
           (lofat-regular-file-p file))
  :hints
  (("goal" :in-theory (enable lofat-file-p lofat-regular-file-p
                              lofat-directory-file-p
                              lofat-file-contents-p
                              lofat-file->contents))))

(defthm
  lofat-fs-p-of-lofat-place-file-lemma-1
  (implies (lofat-file-p file)
           (iff (stringp (lofat-file->contents file))
                (not (lofat-directory-file-p file))))
  :hints
  (("goal" :in-theory (enable lofat-directory-file-p
                              lofat-file-p lofat-file-contents-p
                              lofat-file->contents))))

;; This exists, if I remember correctly, to ensure this file certifies properly
;; even under the default useless-runes settings.
(defthm lofat-remove-file-correctness-lemma-66
  (implies (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                  0)
           (intersectp-equal (mv-nth 0 (d-e-cc fat32$c d-e))
                             (mv-nth 0 (d-e-cc fat32$c d-e)))))

(defthm
  lofat-remove-file-correctness-lemma-23
  (implies
   (good-root-d-e-p root-d-e fat32$c)
   (equal
    (mv-nth
     1
     (update-dir-contents
      fat32$c (d-e-first-cluster root-d-e)
      (nats=>string
       (clear-d-e (string=>nats (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                  name))))
    0))
  :hints
  (("goal" :do-not-induct t
    :in-theory (enable (:rewrite lofat-to-hifat-inversion-lemma-4)
                       lofat-to-hifat-inversion-lemma-15
                       good-root-d-e-p))))

(defthm
  lofat-remove-file-correctness-lemma-31
  (implies
   (and
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
           0)
    (< (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit1)))
       x)
    (>= (nfix entry-limit2)
        (mv-nth 1
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
   (< (hifat-entry-count
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit2)))
      x))
  :hints (("goal" :do-not-induct t
           :use lofat-to-hifat-helper-correctness-4)))

(local
 (defthm
   lofat-remove-file-correctness-lemma-14
   (implies
    (and
     (< x
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
     (equal (mv-nth 3
                    (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
            0)
     (>= (nfix entry-limit2)
         (mv-nth 1
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
    (< x
       (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit2)))))
   :hints (("goal" :do-not-induct t
            :use lofat-to-hifat-helper-correctness-4))))

(defthm
  lofat-place-file-correctness-lemma-38
  (implies
   (and
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit1))
     0)
    (>=
     (nfix entry-limit2)
     (mv-nth
      1
      (lofat-to-hifat-helper fat32$c
                             d-e-list entry-limit1))))
   (subsetp-equal
    (mv-nth 2
            (lofat-to-hifat-helper fat32$c
                                   d-e-list entry-limit2))
    (mv-nth 2
            (lofat-to-hifat-helper fat32$c
                                   d-e-list entry-limit1))))
  :hints (("goal" :do-not-induct t
           :use lofat-to-hifat-helper-correctness-4)))

(encapsulate
  ()

  (local
   (defthm
     lemma
     (implies
      (and
       (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
       (useful-d-e-list-p d-e-list)
       (equal (mv-nth 3
                      (lofat-to-hifat-helper fat32$c
                                             d-e-list entry-limit1))
              0)
       (<=
        (mv-nth
         1
         (lofat-to-hifat-helper
          fat32$c
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents
                    fat32$c
                    (mv-nth 0 (find-d-e d-e-list name)))))
          entry-limit1))
        (nfix entry-limit2))
       (subsetp-equal
        (mv-nth 2
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents
                           fat32$c
                           (mv-nth 0 (find-d-e d-e-list name)))))
                 entry-limit1))
        y))
      (subsetp-equal
       (mv-nth 2
               (lofat-to-hifat-helper
                fat32$c
                (make-d-e-list
                 (mv-nth 0
                         (d-e-cc-contents
                          fat32$c
                          (mv-nth 0 (find-d-e d-e-list name)))))
                entry-limit2))
       y))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (disable lofat-find-file-correctness-1-lemma-6)
       :use
       ((:instance lofat-find-file-correctness-1-lemma-6
                   (entry-limit entry-limit1))
        (:instance
         lofat-to-hifat-helper-correctness-4
         (d-e-list
          (make-d-e-list
           (mv-nth 0
                   (d-e-cc-contents
                    fat32$c
                    (mv-nth 0
                            (find-d-e d-e-list name))))))))))))

  (defthm
    lofat-place-file-correctness-lemma-71
    (implies
     (and (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
          (equal (mv-nth 3
                         (lofat-to-hifat-helper fat32$c
                                                d-e-list entry-limit))
                 0)
          (useful-d-e-list-p d-e-list))
     (subsetp-equal
      (mv-nth
       2
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents
                  fat32$c
                  (mv-nth 0 (find-d-e d-e-list name)))))
        entry-limit))
      (mv-nth 2
              (lofat-to-hifat-helper fat32$c
                                     d-e-list entry-limit))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (lofat-to-hifat-helper find-d-e)
       ((:rewrite nfix-when-zp)
        (:rewrite nth-of-nats=>chars)
        (:definition natp)
        (:rewrite nth-of-effective-fat)
        (:linear nth-when-d-e-p)
        (:rewrite explode-of-d-e-filename)
        (:rewrite
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
        (:rewrite d-e-p-when-member-equal-of-d-e-list-p)
        (:rewrite take-of-len-free)
        (:rewrite natp-of-car-when-nat-listp)))
      :induct (lofat-to-hifat-helper fat32$c
                                     d-e-list entry-limit)
      :do-not-induct t))))

(defthm
  lofat-remove-file-correctness-lemma-10
  (implies
   (and (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
               0)
        (>= (nfix entry-limit2)
            (mv-nth 1
                    (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
   (equal
    (equal
     (m1-file-hifat-file-alist-fix
      d-e
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit2)))
     (m1-file-hifat-file-alist-fix
      d-e
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
    t))
  :hints (("goal" :use lofat-to-hifat-helper-correctness-4)))

(encapsulate
  ()

  (local
   (in-theory
    (disable
     (:rewrite not-intersectp-list-when-subsetp-2)
     (:rewrite subsetp-when-atom-right)
     (:rewrite subsetp-car-member)
     (:rewrite subsetp-trans2)
     (:rewrite subsetp-trans)
     (:rewrite member-of-append)
     (:rewrite
      not-intersectp-list-of-set-difference$-lemma-2
      . 1)
     (:rewrite
      not-intersectp-list-of-set-difference$-lemma-1)
     (:rewrite natp-of-car-when-nat-listp)
     (:definition binary-append)
     (:rewrite
      d-e-p-when-member-equal-of-d-e-list-p)
     (:rewrite
      lofat-to-hifat-helper-of-update-dir-contents)
     (:rewrite
      fat32-build-index-list-of-effective-fat-of-place-contents-disjoint)
     (:rewrite
      nat-listp-if-fat32-masked-entry-list-p)
     (:rewrite len-of-insert-d-e)
     (:rewrite
      d-e-cc-of-clear-cc)
     (:rewrite place-contents-expansion-2)
     (:rewrite len-of-place-d-e)
     (:rewrite member-when-atom)
     (:rewrite
      useful-d-e-list-p-of-place-d-e)
     (:rewrite fat32-filename-p-correctness-1)
     (:rewrite
      lofat-to-hifat-helper-of-clear-cc)
     (:rewrite
      d-e-cc-of-update-dir-contents)
     (:rewrite
      d-e-cc-contents-of-update-dir-contents-disjoint)
     (:rewrite put-assoc-equal-without-change . 2)
     (:rewrite len-of-find-n-free-clusters)
     (:rewrite
      d-e-cc-contents-of-clear-cc)
     (:definition
      stobj-find-n-free-clusters-correctness-1))))

  (local
   (defun-nx
     induction-scheme
     (d-e-list entry-limit fat32$c x)
     (cond
      ((and
        (not (atom d-e-list))
        (not (zp entry-limit))
        (d-e-directory-p (car d-e-list))
        (>= (d-e-first-cluster (car d-e-list))
            2)
        (> (+ (count-of-clusters fat32$c)
              2)
           (d-e-first-cluster (car d-e-list))))
       (induction-scheme
        (cdr d-e-list)
        (+
         entry-limit
         (-
          (+
           1
           (hifat-entry-count
            (mv-nth
             0
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents
                        fat32$c (car d-e-list))))
              (+ -1 entry-limit)))))))
        fat32$c
        (append
         (mv-nth 0
                 (d-e-cc
                  fat32$c (car d-e-list)))
         (flatten
          (mv-nth
           2
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents
                      fat32$c (car d-e-list))))
            (+ -1 entry-limit))))
         x)))
      ((and
        (not (atom d-e-list))
        (not (zp entry-limit))
        ;; (not (d-e-directory-p (car d-e-list)))
        (>= (d-e-first-cluster (car d-e-list))
            2)
        (> (+ (count-of-clusters fat32$c)
              2)
           (d-e-first-cluster (car d-e-list))))
       (induction-scheme
        (cdr d-e-list)
        (- entry-limit 1)
        fat32$c
        (append
         (mv-nth 0
                 (d-e-cc
                  fat32$c (car d-e-list)))
         x)))
      ((and
        (not (atom d-e-list))
        (not (zp entry-limit)))
       (induction-scheme
        (cdr d-e-list)
        (- entry-limit 1)
        fat32$c
        x))
      (t
       (mv d-e-list entry-limit fat32$c x)))))

  (defthm
    lofat-place-file-correctness-lemma-30
    (implies
     (and
      (equal (mv-nth 1 (find-d-e d-e-list filename))
             0)
      (< 0
         (len (explode (lofat-file->contents file))))
      (lofat-fs-p fat32$c)
      (useful-d-e-list-p d-e-list)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c
                                            d-e-list entry-limit))
             0)
      (lofat-regular-file-p file)
      (non-free-index-listp x (effective-fat fat32$c))
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c
                                      d-e-list entry-limit)))
      (<= 2
          (d-e-first-cluster (mv-nth 0
                                     (find-d-e d-e-list filename))))
      (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename)))
         (+ 2 (count-of-clusters fat32$c)))
      (not (d-e-directory-p (mv-nth 0
                                    (find-d-e d-e-list filename))))
      (zp
       (mv-nth
        2
        (place-contents
         (update-fati
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth 0
                     (d-e-cc
                      fat32$c
                      (mv-nth 0
                              (find-d-e d-e-list filename))))
             (make-list-ac
              (len (mv-nth 0
                           (d-e-cc
                            fat32$c
                            (mv-nth 0
                                    (find-d-e d-e-list filename)))))
              0 nil))
            1))
          (fat32-update-lower-28
           (fati
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth 0
                       (d-e-cc
                        fat32$c
                        (mv-nth 0
                                (find-d-e d-e-list filename))))
               (make-list-ac
                (len
                 (mv-nth 0
                         (d-e-cc
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list filename)))))
                0 nil))
              1))
            fat32$c)
           268435455)
          (mv-nth
           0
           (clear-cc
            fat32$c
            (d-e-first-cluster
             (mv-nth 0 (find-d-e d-e-list filename)))
            (d-e-file-size (mv-nth 0
                                   (find-d-e d-e-list filename))))))
         (mv-nth 0 (find-d-e d-e-list filename))
         (lofat-file->contents file)
         (len (explode (lofat-file->contents file)))
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth 0
                    (d-e-cc
                     fat32$c
                     (mv-nth 0
                             (find-d-e d-e-list filename))))
            (make-list-ac
             (len (mv-nth 0
                          (d-e-cc
                           fat32$c
                           (mv-nth 0
                                   (find-d-e d-e-list filename)))))
             0 nil))
           1))))))
     (and
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth
          0
          (place-contents
           (update-fati
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth 0
                       (d-e-cc
                        fat32$c
                        (mv-nth 0
                                (find-d-e d-e-list filename))))
               (make-list-ac
                (len
                 (mv-nth 0
                         (d-e-cc
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list filename)))))
                0 nil))
              1))
            (fat32-update-lower-28
             (fati
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth 0
                         (d-e-cc
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list filename))))
                 (make-list-ac
                  (len
                   (mv-nth 0
                           (d-e-cc
                            fat32$c
                            (mv-nth 0
                                    (find-d-e d-e-list filename)))))
                  0 nil))
                1))
              fat32$c)
             268435455)
            (mv-nth 0
                    (clear-cc
                     fat32$c
                     (d-e-first-cluster
                      (mv-nth 0 (find-d-e d-e-list filename)))
                     (d-e-file-size
                      (mv-nth 0
                              (find-d-e d-e-list filename))))))
           (mv-nth 0 (find-d-e d-e-list filename))
           (lofat-file->contents file)
           (len (explode (lofat-file->contents file)))
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth 0
                      (d-e-cc
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename))))
              (make-list-ac
               (len
                (mv-nth 0
                        (d-e-cc
                         fat32$c
                         (mv-nth 0
                                 (find-d-e d-e-list filename)))))
               0 nil))
             1))))
         (place-d-e
          d-e-list
          (d-e-set-first-cluster-file-size
           (mv-nth 0 (find-d-e d-e-list filename))
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth 0
                      (d-e-cc
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename))))
              (make-list-ac
               (len
                (mv-nth 0
                        (d-e-cc
                         fat32$c
                         (mv-nth 0
                                 (find-d-e d-e-list filename)))))
               0 nil))
             1))
           (len (explode (lofat-file->contents file)))))
         entry-limit)))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth
          0
          (place-contents
           (update-fati
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth 0
                       (d-e-cc
                        fat32$c
                        (mv-nth 0
                                (find-d-e d-e-list filename))))
               (make-list-ac
                (len
                 (mv-nth 0
                         (d-e-cc
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list filename)))))
                0 nil))
              1))
            (fat32-update-lower-28
             (fati
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth 0
                         (d-e-cc
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list filename))))
                 (make-list-ac
                  (len
                   (mv-nth 0
                           (d-e-cc
                            fat32$c
                            (mv-nth 0
                                    (find-d-e d-e-list filename)))))
                  0 nil))
                1))
              fat32$c)
             268435455)
            (mv-nth 0
                    (clear-cc
                     fat32$c
                     (d-e-first-cluster
                      (mv-nth 0 (find-d-e d-e-list filename)))
                     (d-e-file-size
                      (mv-nth 0
                              (find-d-e d-e-list filename))))))
           (mv-nth 0 (find-d-e d-e-list filename))
           (lofat-file->contents file)
           (len (explode (lofat-file->contents file)))
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth 0
                      (d-e-cc
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename))))
              (make-list-ac
               (len
                (mv-nth 0
                        (d-e-cc
                         fat32$c
                         (mv-nth 0
                                 (find-d-e d-e-list filename)))))
               0 nil))
             1))))
         (place-d-e
          d-e-list
          (d-e-set-first-cluster-file-size
           (mv-nth 0 (find-d-e d-e-list filename))
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth 0
                      (d-e-cc
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename))))
              (make-list-ac
               (len
                (mv-nth 0
                        (d-e-cc
                         fat32$c
                         (mv-nth 0
                                 (find-d-e d-e-list filename)))))
               0 nil))
             1))
           (len (explode (lofat-file->contents file)))))
         entry-limit))
       0)
      (equal
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (place-contents
           (update-fati
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth 0
                       (d-e-cc
                        fat32$c
                        (mv-nth 0
                                (find-d-e d-e-list filename))))
               (make-list-ac
                (len
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth 0
                           (find-d-e d-e-list filename)))))
                0 nil))
              1))
            (fat32-update-lower-28
             (fati
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth
                  0
                  (d-e-cc
                   fat32$c
                   (mv-nth 0
                           (find-d-e d-e-list filename))))
                 (make-list-ac
                  (len
                   (mv-nth
                    0
                    (d-e-cc
                     fat32$c
                     (mv-nth 0
                             (find-d-e d-e-list filename)))))
                  0 nil))
                1))
              fat32$c)
             268435455)
            (mv-nth
             0
             (clear-cc
              fat32$c
              (d-e-first-cluster
               (mv-nth 0 (find-d-e d-e-list filename)))
              (d-e-file-size
               (mv-nth 0
                       (find-d-e d-e-list filename))))))
           (mv-nth 0 (find-d-e d-e-list filename))
           (lofat-file->contents file)
           (len (explode (lofat-file->contents file)))
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth 0
                      (d-e-cc
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth 0
                          (find-d-e d-e-list filename)))))
               0 nil))
             1))))
         (place-d-e
          d-e-list
          (d-e-set-first-cluster-file-size
           (mv-nth 0 (find-d-e d-e-list filename))
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth 0
                      (d-e-cc
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename))))
              (make-list-ac
               (len
                (mv-nth
                 0
                 (d-e-cc
                  fat32$c
                  (mv-nth 0
                          (find-d-e d-e-list filename)))))
               0 nil))
             1))
           (len (explode (lofat-file->contents file)))))
         entry-limit))
       (put-assoc-equal
        filename
        (m1-file
         (d-e-set-first-cluster-file-size
          (mv-nth 0 (find-d-e d-e-list filename))
          (nth 0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth 0
                         (d-e-cc
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list filename))))
                 (make-list-ac
                  (len
                   (mv-nth 0
                           (d-e-cc
                            fat32$c
                            (mv-nth 0
                                    (find-d-e d-e-list filename)))))
                  0 nil))
                1))
          (len (explode (lofat-file->contents file))))
         (lofat-file->contents file))
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit))))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (lofat-to-hifat-helper not-intersectp-list
                              (:rewrite len-of-find-n-free-clusters))
       ((:rewrite nth-of-nats=>chars)
        (:linear nth-when-d-e-p)
        (:rewrite explode-of-d-e-filename)
        (:rewrite take-of-len-free)
        (:rewrite lofat-to-hifat-helper-of-clear-cc)
        (:rewrite subdir-contents-p-when-zero-length)
        (:linear lofat-to-hifat-helper-correctness-3)
        (:rewrite lofat-place-file-correctness-lemma-56)
        (:rewrite d-e-cc-under-iff . 2)
        (:rewrite consp-of-find-n-free-clusters)
        (:definition len)
        (:rewrite intersectp-when-subsetp)
        (:rewrite subsetp-when-atom-left)
        (:rewrite intersectp-equal-of-atom-left)
        (:rewrite lofat-place-file-correctness-lemma-58)
        (:linear lofat-place-file-correctness-1-lemma-25)
        (:rewrite nth-of-set-indices-in-fa-table-when-member)
        (:rewrite lofat-place-file-correctness-lemma-18)
        (:rewrite lofat-place-file-correctness-lemma-121
                  . 2)
        (:rewrite lofat-place-file-correctness-lemma-121
                  . 1)
        (:rewrite consp-of-fat32-build-index-list)))
      :induct (induction-scheme d-e-list
                                entry-limit fat32$c x)
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c
                                             d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c
                           d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c
                                             (cons d-e d-e-list)
                                             entry-limit)))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and
        (equal (mv-nth 1 (find-d-e d-e-list filename))
               0)
        (< 0
           (len (explode (lofat-file->contents file))))
        (lofat-fs-p fat32$c)
        (useful-d-e-list-p d-e-list)
        (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0)
        (lofat-regular-file-p file)
        (non-free-index-listp x (effective-fat fat32$c))
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c
                                        d-e-list entry-limit)))
        (<= 2
            (d-e-first-cluster (mv-nth 0
                                       (find-d-e d-e-list filename))))
        (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename)))
           (+ 2 (count-of-clusters fat32$c)))
        (not (d-e-directory-p (mv-nth 0
                                      (find-d-e d-e-list filename))))
        (zp
         (mv-nth
          2
          (place-contents
           (update-fati
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth 0
                       (d-e-cc
                        fat32$c
                        (mv-nth 0
                                (find-d-e d-e-list filename))))
               (make-list-ac
                (len (mv-nth 0
                             (d-e-cc
                              fat32$c
                              (mv-nth 0
                                      (find-d-e d-e-list filename)))))
                0 nil))
              1))
            (fat32-update-lower-28
             (fati
              (nth
               0
               (find-n-free-clusters
                (set-indices-in-fa-table
                 (effective-fat fat32$c)
                 (mv-nth 0
                         (d-e-cc
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list filename))))
                 (make-list-ac
                  (len
                   (mv-nth 0
                           (d-e-cc
                            fat32$c
                            (mv-nth 0
                                    (find-d-e d-e-list filename)))))
                  0 nil))
                1))
              fat32$c)
             268435455)
            (mv-nth
             0
             (clear-cc
              fat32$c
              (d-e-first-cluster
               (mv-nth 0 (find-d-e d-e-list filename)))
              (d-e-file-size (mv-nth 0
                                     (find-d-e d-e-list filename))))))
           (mv-nth 0 (find-d-e d-e-list filename))
           (lofat-file->contents file)
           (len (explode (lofat-file->contents file)))
           (nth
            0
            (find-n-free-clusters
             (set-indices-in-fa-table
              (effective-fat fat32$c)
              (mv-nth 0
                      (d-e-cc
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename))))
              (make-list-ac
               (len (mv-nth 0
                            (d-e-cc
                             fat32$c
                             (mv-nth 0
                                     (find-d-e d-e-list filename)))))
               0 nil))
             1))))))
       (not-intersectp-list
        x
        (mv-nth
         2
         (lofat-to-hifat-helper
          (mv-nth
           0
           (place-contents
            (update-fati
             (nth
              0
              (find-n-free-clusters
               (set-indices-in-fa-table
                (effective-fat fat32$c)
                (mv-nth 0
                        (d-e-cc
                         fat32$c
                         (mv-nth 0
                                 (find-d-e d-e-list filename))))
                (make-list-ac
                 (len
                  (mv-nth 0
                          (d-e-cc
                           fat32$c
                           (mv-nth 0
                                   (find-d-e d-e-list filename)))))
                 0 nil))
               1))
             (fat32-update-lower-28
              (fati
               (nth
                0
                (find-n-free-clusters
                 (set-indices-in-fa-table
                  (effective-fat fat32$c)
                  (mv-nth 0
                          (d-e-cc
                           fat32$c
                           (mv-nth 0
                                   (find-d-e d-e-list filename))))
                  (make-list-ac
                   (len
                    (mv-nth 0
                            (d-e-cc
                             fat32$c
                             (mv-nth 0
                                     (find-d-e d-e-list filename)))))
                   0 nil))
                 1))
               fat32$c)
              268435455)
             (mv-nth 0
                     (clear-cc
                      fat32$c
                      (d-e-first-cluster
                       (mv-nth 0 (find-d-e d-e-list filename)))
                      (d-e-file-size
                       (mv-nth 0
                               (find-d-e d-e-list filename))))))
            (mv-nth 0 (find-d-e d-e-list filename))
            (lofat-file->contents file)
            (len (explode (lofat-file->contents file)))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth 0
                       (d-e-cc
                        fat32$c
                        (mv-nth 0
                                (find-d-e d-e-list filename))))
               (make-list-ac
                (len
                 (mv-nth 0
                         (d-e-cc
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list filename)))))
                0 nil))
              1))))
          (place-d-e
           d-e-list
           (d-e-set-first-cluster-file-size
            (mv-nth 0 (find-d-e d-e-list filename))
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth 0
                       (d-e-cc
                        fat32$c
                        (mv-nth 0
                                (find-d-e d-e-list filename))))
               (make-list-ac
                (len
                 (mv-nth 0
                         (d-e-cc
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list filename)))))
                0 nil))
              1))
            (len (explode (lofat-file->contents file)))))
          entry-limit)))))))

  (defthm
    lofat-place-file-correctness-lemma-158
    (implies
     (and
      (<= 2 i)
      (fat32-masked-entry-p i)
      (zp (fat32-entry-mask (fati i fat32$c)))
      (< i (+ 2 (count-of-clusters fat32$c)))
      (non-free-index-listp x (effective-fat fat32$c))
      (d-e-p d-e)
      (lofat-fs-p fat32$c)
      (integerp entry-limit)
      (>
       entry-limit
       (mv-nth
        1
        (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
       0)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
      (zp
       (mv-nth
        2
        (place-contents
         (update-fati i
                      (fat32-update-lower-28 (fati i fat32$c)
                                             268435455)
                      fat32$c)
         (d-e-install-directory-bit (make-d-e-with-filename name)
                                    t)
         (make-empty-subdir-contents i (d-e-first-cluster d-e))
         0 i)))
      (useful-d-e-list-p d-e-list)
      ;; This hypothesis doesn't actually apply to all corollaries, but we can
      ;; sort that out later.
      (fat32-filename-p name))
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth
          0
          (place-contents
           (update-fati i
                        (fat32-update-lower-28 (fati i fat32$c)
                                               268435455)
                        fat32$c)
           (d-e-install-directory-bit
            (make-d-e-with-filename name)
            t)
           (make-empty-subdir-contents i (d-e-first-cluster d-e))
           0 i))
         (place-d-e d-e-list
                    (d-e-set-first-cluster-file-size
                     (d-e-install-directory-bit
                      (make-d-e-with-filename name)
                      t)
                     i 0))
         entry-limit))
       0)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth
          0
          (place-contents
           (update-fati i
                        (fat32-update-lower-28 (fati i fat32$c)
                                               268435455)
                        fat32$c)
           (d-e-install-directory-bit
            (make-d-e-with-filename name)
            t)
           (make-empty-subdir-contents i (d-e-first-cluster d-e))
           0 i))
         (place-d-e d-e-list
                    (d-e-set-first-cluster-file-size
                     (d-e-install-directory-bit
                      (make-d-e-with-filename name)
                      t)
                     i 0))
         entry-limit)))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (place-contents
           (update-fati i
                        (fat32-update-lower-28 (fati i fat32$c)
                                               268435455)
                        fat32$c)
           (d-e-install-directory-bit
            (make-d-e-with-filename name)
            t)
           (make-empty-subdir-contents i (d-e-first-cluster d-e))
           0 i))
         (place-d-e d-e-list
                    (d-e-set-first-cluster-file-size
                     (d-e-install-directory-bit
                      (make-d-e-with-filename name)
                      t)
                     i 0))
         entry-limit))
       (put-assoc-equal
        name
        (m1-file-hifat-file-alist-fix d-e nil)
        (mv-nth
         0
         (lofat-to-hifat-helper
          fat32$c
          d-e-list
          entry-limit))))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (not-intersectp-list hifat-entry-count
                            place-d-e lofat-to-hifat-helper)
       ((:e make-list-ac)
        (:definition subseq)
        (:definition subseq-list)
        (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
        (:rewrite nfix-when-zp)
        (:definition delete-d-e)
        (:rewrite nth-of-nats=>chars)
        (:rewrite take-of-len-free)
        (:rewrite nats=>chars-of-take)
        (:rewrite d-e-cc-under-iff . 2)
        (:rewrite intersectp-when-subsetp)
        (:rewrite disjoint-list-listp-of-lofat-to-hifat-helper)
        (:rewrite not-intersectp-list-of-set-difference$)
        (:rewrite not-intersectp-list-when-atom)
        (:rewrite lofat-find-file-correctness-1-lemma-6)
        (:rewrite m1-file-p-of-cdar-when-m1-file-alist-p)
        (:rewrite fat32-filename-p-correctness-1)
        (:definition assoc-equal)
        (:rewrite fat32-filename-p-of-caar-when-m1-file-alist-p)
        (:rewrite car-of-append)
        (:rewrite subdir-contents-p-when-zero-length)
        (:rewrite hifat-no-dups-p-of-cdr)
        (:type-prescription binary-append)
        (:type-prescription intersectp-equal)
        (:rewrite intersectp-member . 1)
        (:rewrite intersect-with-subset . 6)
        (:rewrite intersect-with-subset . 5)
        (:rewrite intersect-with-subset . 11)
        (:rewrite intersect-with-subset . 9)
        (:rewrite consp-of-append)
        (:rewrite not-intersectp-list-of-set-difference$-lemma-3)
        (:rewrite member-intersectp-with-subset)
        (:rewrite d-e-cc-under-iff . 3)
        (:rewrite subsetp-when-atom-right)
        (:rewrite subsetp-when-atom-left)
        (:rewrite append-atom-under-list-equiv)
        (:rewrite lofat-place-file-correctness-lemma-5)
        (:rewrite rationalp-implies-acl2-numberp)
        (:rewrite consp-of-remove-assoc-1)
        (:rewrite member-intersectp-of-set-difference$-1
                  . 1)
        (:rewrite hifat-to-lofat-inversion-lemma-23)
        (:rewrite place-contents-expansion-2)
        (:rewrite nthcdr-when->=-n-len-l)
        (:rewrite d-e-p-of-take)
        (:linear len-of-explode-when-m1-file-contents-p-1)
        (:definition nthcdr)
        (:rewrite then-subseq-empty-1)
        (:linear length-of-d-e-cc-contents . 3)
        (:rewrite unsigned-byte-listp-when-d-e-p)
        (:rewrite d-e-p-of-chars=>nats)
        (:rewrite chars=>nats-of-take)
        (:type-prescription hifat-bounded-file-alist-p)
        (:rewrite take-when-atom)
        (:definition char)
        (:rewrite explode-of-d-e-filename)
        (:linear len-when-hifat-bounded-file-alist-p . 2)
        (:linear len-when-hifat-bounded-file-alist-p . 1)
        (:linear length-of-d-e-cc-contents . 2)
        (:rewrite effective-fat-of-clear-cc . 3)
        (:rewrite find-n-free-clusters-when-zp)
        (:rewrite str::consp-of-explode)
        (:rewrite hifat-to-lofat-inversion-lemma-2)
        (:rewrite m1-regular-file-p-correctness-1)
        (:type-prescription m1-file-fix$inline)
        (:rewrite place-contents-expansion-1)
        (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
        (:type-prescription fat32-filename-fix)
        (:rewrite lofat-directory-file-p-when-lofat-file-p)
        (:rewrite fati-of-clear-cc . 3)
        (:rewrite m1-file-p-of-m1-file-fix)
        (:rewrite natp-of-place-contents)
        (:rewrite len-of-find-n-free-clusters)
        (:linear find-n-free-clusters-correctness-7)
        (:rewrite str::explode-when-not-stringp)
        (:definition stobj-find-n-free-clusters-correctness-1)
        (:rewrite set-difference$-when-not-intersectp)
        (:rewrite subsetp-member . 1)
        (:rewrite delete-d-e-correctness-1)
        (:definition remove-assoc-equal)
        (:rewrite abs-find-file-correctness-1-lemma-40)
        (:rewrite hifat-place-file-correctness-3)
        (:rewrite remove-assoc-when-absent-1)
        (:rewrite
         hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
        (:rewrite
         d-e-cc-contents-of-lofat-place-file-coincident-lemma-15)
        (:rewrite not-intersectp-list-when-subsetp-1)
        (:rewrite m1-directory-file-p-when-m1-file-p)
        (:rewrite m1-file-fix-when-m1-file-p)
        (:rewrite m1-directory-file-p-correctness-1)))
      :induct (induction-scheme d-e-list entry-limit fat32$c x)
      :expand
      ((:free
        (fat32$c entry-limit)
        (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
       (:free (x1 x2 y)
              (not-intersectp-list x1 (cons x2 y)))
       (:free (d-e fat32$c d-e-list entry-limit)
              (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                     entry-limit))
       (find-d-e d-e-list name))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and
        (<= 2 i)
        (fat32-masked-entry-p i)
        (zp (fat32-entry-mask (fati i fat32$c)))
        (< i (+ 2 (count-of-clusters fat32$c)))
        (non-free-index-listp x (effective-fat fat32$c))
        (d-e-p d-e)
        (lofat-fs-p fat32$c)
        (integerp entry-limit)
        (>
         entry-limit
         (mv-nth
          1
          (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
        (equal
         (mv-nth
          3
          (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
         0)
        (not-intersectp-list
         x
         (mv-nth
          2
          (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
        (zp
         (mv-nth
          2
          (place-contents
           (update-fati i
                        (fat32-update-lower-28 (fati i fat32$c)
                                               268435455)
                        fat32$c)
           (d-e-install-directory-bit
            (make-d-e-with-filename name)
            t)
           (make-empty-subdir-contents i (d-e-first-cluster d-e))
           0 i)))
        (useful-d-e-list-p d-e-list)
        (fat32-filename-p name))
       (not-intersectp-list
        x
        (mv-nth
         2
         (lofat-to-hifat-helper
          (mv-nth
           0
           (place-contents
            (update-fati i
                         (fat32-update-lower-28 (fati i fat32$c)
                                                268435455)
                         fat32$c)
            (d-e-install-directory-bit
             (make-d-e-with-filename name)
             t)
            (make-empty-subdir-contents
             i (d-e-first-cluster d-e))
            0 i))
          (place-d-e d-e-list
                     (d-e-set-first-cluster-file-size
                      (d-e-install-directory-bit
                       (make-d-e-with-filename name)
                       t)
                      i 0))
          entry-limit)))))))

  (defthm
    lofat-place-file-correctness-lemma-171
    (implies
     (and
      (lofat-fs-p fat32$c)
      (useful-d-e-list-p d-e-list)
      (fat32-masked-entry-p i)
      (<= *ms-first-data-cluster* i)
      (zp
       (fat32-entry-mask
        (nth
         i
         (effective-fat
          (mv-nth
           0
           (clear-cc fat32$c
                     (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
                     2097152))))))
      (zp (mv-nth 3
                  (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
      (> (+ 2 (count-of-clusters fat32$c)) i)
      (zp
       (mv-nth
        2
        (place-contents
         (update-fati
          i
          (fat32-update-lower-28 (fati i fat32$c)
                                 268435455)
          (mv-nth
           0
           (clear-cc fat32$c
                     (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
                     2097152)))
         (mv-nth 0 (find-d-e d-e-list name))
         (make-empty-subdir-contents i (d-e-first-cluster d-e))
         0 i)))
      (not-intersectp-list
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
      (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
      (<= *ms-first-data-cluster*
          (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name))))
      (d-e-p d-e)
      (non-free-index-listp x (effective-fat fat32$c)))
     (and
      (equal
       (mv-nth
        3
        (lofat-to-hifat-helper
         (mv-nth
          0
          (place-contents
           (update-fati
            i
            (fat32-update-lower-28 (fati i fat32$c)
                                   268435455)
            (mv-nth
             0
             (clear-cc fat32$c
                       (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
                       2097152)))
           (mv-nth 0 (find-d-e d-e-list name))
           (make-empty-subdir-contents i (d-e-first-cluster d-e))
           0 i))
         (place-d-e
          d-e-list
          (d-e-set-first-cluster-file-size (mv-nth 0 (find-d-e d-e-list name))
                                           i 0))
         entry-limit))
       0)
      (not-intersectp-list
       x
       (mv-nth
        2
        (lofat-to-hifat-helper
         (mv-nth
          0
          (place-contents
           (update-fati
            i
            (fat32-update-lower-28 (fati i fat32$c)
                                   268435455)
            (mv-nth
             0
             (clear-cc fat32$c
                       (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
                       2097152)))
           (mv-nth 0 (find-d-e d-e-list name))
           (make-empty-subdir-contents i (d-e-first-cluster d-e))
           0 i))
         (place-d-e
          d-e-list
          (d-e-set-first-cluster-file-size (mv-nth 0 (find-d-e d-e-list name))
                                           i 0))
         entry-limit)))
      (hifat-equiv
       (mv-nth
        0
        (lofat-to-hifat-helper
         (mv-nth
          0
          (place-contents
           (update-fati
            i
            (fat32-update-lower-28 (fati i fat32$c)
                                   268435455)
            (mv-nth
             0
             (clear-cc fat32$c
                       (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
                       2097152)))
           (mv-nth 0 (find-d-e d-e-list name))
           (make-empty-subdir-contents i (d-e-first-cluster d-e))
           0 i))
         (place-d-e
          d-e-list
          (d-e-set-first-cluster-file-size (mv-nth 0 (find-d-e d-e-list name))
                                           i 0))
         entry-limit))
       (put-assoc-equal
        name
        (m1-file-hifat-file-alist-fix d-e nil)
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))))
    :hints
    (("goal"
      :in-theory
      (e/d (not-intersectp-list place-d-e)
           ((:definition subseq)
            (:definition subseq-list)
            (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
            (:rewrite nfix-when-zp)
            (:definition delete-d-e)
            (:rewrite nth-of-nats=>chars)
            (:rewrite take-of-len-free)
            (:rewrite nats=>chars-of-take)
            (:rewrite disjoint-list-listp-of-lofat-to-hifat-helper)
            (:rewrite not-intersectp-list-of-set-difference$)
            (:rewrite lofat-find-file-correctness-1-lemma-6)
            (:rewrite m1-file-p-of-cdar-when-m1-file-alist-p)
            (:rewrite fat32-filename-p-correctness-1)
            (:definition assoc-equal)
            (:rewrite fat32-filename-p-of-caar-when-m1-file-alist-p)
            (:rewrite car-of-append)
            (:rewrite subdir-contents-p-when-zero-length)
            (:rewrite hifat-no-dups-p-of-cdr)
            (:type-prescription binary-append)
            (:type-prescription intersectp-equal)
            (:rewrite intersectp-member . 1)
            (:rewrite intersect-with-subset . 6)
            (:rewrite intersect-with-subset . 5)
            (:rewrite intersect-with-subset . 11)
            (:rewrite intersect-with-subset . 9)
            (:rewrite consp-of-append)
            (:rewrite not-intersectp-list-of-set-difference$-lemma-3)
            (:rewrite member-intersectp-with-subset)
            (:rewrite subsetp-when-atom-right)
            (:rewrite append-atom-under-list-equiv)
            (:rewrite lofat-place-file-correctness-lemma-5)
            (:rewrite rationalp-implies-acl2-numberp)
            (:rewrite consp-of-remove-assoc-1)
            (:rewrite member-intersectp-of-set-difference$-1
                      . 1)
            (:rewrite hifat-to-lofat-inversion-lemma-23)
            (:rewrite nthcdr-when->=-n-len-l)
            (:rewrite d-e-p-of-take)
            (:linear len-of-explode-when-m1-file-contents-p-1)
            (:definition nthcdr)
            (:rewrite then-subseq-empty-1)
            (:linear length-of-d-e-cc-contents . 3)
            (:rewrite unsigned-byte-listp-when-d-e-p)
            (:rewrite d-e-p-of-chars=>nats)
            (:rewrite chars=>nats-of-take)
            (:type-prescription hifat-bounded-file-alist-p)
            (:rewrite take-when-atom)
            (:definition char)
            (:rewrite explode-of-d-e-filename)
            (:linear len-when-hifat-bounded-file-alist-p . 2)
            (:linear len-when-hifat-bounded-file-alist-p . 1)
            (:linear length-of-d-e-cc-contents . 2)
            (:rewrite effective-fat-of-clear-cc . 3)
            (:rewrite str::consp-of-explode)
            (:rewrite hifat-to-lofat-inversion-lemma-2)
            (:rewrite m1-regular-file-p-correctness-1)
            (:type-prescription m1-file-fix$inline)
            (:rewrite place-contents-expansion-1)
            (:rewrite lofat-to-hifat-helper-of-update-dir-contents)
            (:type-prescription fat32-filename-fix)
            (:rewrite lofat-directory-file-p-when-lofat-file-p)
            (:rewrite m1-file-p-of-m1-file-fix)
            (:rewrite natp-of-place-contents)
            (:rewrite len-of-find-n-free-clusters)
            (:linear find-n-free-clusters-correctness-7)
            (:rewrite str::explode-when-not-stringp)
            (:definition min)
            (:rewrite set-difference$-when-not-intersectp)
            (:rewrite delete-d-e-correctness-1)
            (:definition remove-assoc-equal)
            (:rewrite abs-find-file-correctness-1-lemma-40)
            (:rewrite hifat-place-file-correctness-3)
            (:rewrite remove-assoc-when-absent-1)
            (:definition find-d-e)
            (:rewrite m1-directory-file-p-when-m1-file-p)
            (:rewrite m1-file-fix-when-m1-file-p)
            (:rewrite m1-directory-file-p-correctness-1)))
      :induct (induction-scheme d-e-list entry-limit fat32$c x)
      :do-not-induct t
      :expand ((:free (fat32$c entry-limit)
                      (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
               (:free (x1 x2 y)
                      (not-intersectp-list x1 (cons x2 y)))
               (:free (d-e fat32$c d-e-list entry-limit)
                      (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                             entry-limit))
               (find-d-e d-e-list name))))
    :rule-classes
    ((:rewrite
      :corollary
      (implies
       (and
        (lofat-fs-p fat32$c)
        (useful-d-e-list-p d-e-list)
        (fat32-masked-entry-p i)
        (<= *ms-first-data-cluster* i)
        (zp
         (fat32-entry-mask
          (nth
           i
           (effective-fat
            (mv-nth
             0
             (clear-cc fat32$c
                       (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
                       2097152))))))
        (zp (mv-nth 3
                    (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
        (> (+ 2 (count-of-clusters fat32$c)) i)
        (zp
         (mv-nth
          2
          (place-contents
           (update-fati
            i
            (fat32-update-lower-28 (fati i fat32$c)
                                   268435455)
            (mv-nth
             0
             (clear-cc fat32$c
                       (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
                       2097152)))
           (mv-nth 0 (find-d-e d-e-list name))
           (make-empty-subdir-contents i (d-e-first-cluster d-e))
           0 i)))
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
        (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
        (<= *ms-first-data-cluster*
            (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name))))
        (d-e-p d-e)
        (non-free-index-listp x (effective-fat fat32$c)))
       (not-intersectp-list
        x
        (mv-nth
         2
         (lofat-to-hifat-helper
          (mv-nth
           0
           (place-contents
            (update-fati
             i
             (fat32-update-lower-28 (fati i fat32$c)
                                    268435455)
             (mv-nth
              0
              (clear-cc fat32$c
                        (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
                        2097152)))
            (mv-nth 0 (find-d-e d-e-list name))
            (make-empty-subdir-contents i (d-e-first-cluster d-e))
            0 i))
          (place-d-e
           d-e-list
           (d-e-set-first-cluster-file-size (mv-nth 0 (find-d-e d-e-list name))
                                            i 0))
          entry-limit))))))))

(defthm
  lofat-place-file-correctness-lemma-91
  (implies
   (and
    (< 0
       (len (explode (lofat-file->contents file))))
    (lofat-fs-p fat32$c)
    (useful-d-e-list-p d-e-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit))
           0)
    (lofat-regular-file-p file)
    (<= 2
        (d-e-first-cluster (mv-nth 0
                                   (find-d-e d-e-list filename))))
    (< (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list filename)))
       (+ 2 (count-of-clusters fat32$c)))
    (not (d-e-directory-p (mv-nth 0
                                  (find-d-e d-e-list filename))))
    (zp
     (mv-nth
      2
      (place-contents
       (update-fati
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth 0
                   (d-e-cc
                    fat32$c
                    (mv-nth 0
                            (find-d-e d-e-list filename))))
           (make-list-ac
            (len (mv-nth 0
                         (d-e-cc
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list filename)))))
            0 nil))
          1))
        (fat32-update-lower-28
         (fati
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth 0
                     (d-e-cc
                      fat32$c
                      (mv-nth 0
                              (find-d-e d-e-list filename))))
             (make-list-ac
              (len
               (mv-nth 0
                       (d-e-cc
                        fat32$c
                        (mv-nth 0
                                (find-d-e d-e-list filename)))))
              0 nil))
            1))
          fat32$c)
         268435455)
        (mv-nth
         0
         (clear-cc
          fat32$c
          (d-e-first-cluster
           (mv-nth 0 (find-d-e d-e-list filename)))
          (d-e-file-size (mv-nth 0
                                 (find-d-e d-e-list filename))))))
       (mv-nth 0 (find-d-e d-e-list filename))
       (lofat-file->contents file)
       (len (explode (lofat-file->contents file)))
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth 0
                  (d-e-cc
                   fat32$c
                   (mv-nth 0
                           (find-d-e d-e-list filename))))
          (make-list-ac
           (len (mv-nth 0
                        (d-e-cc
                         fat32$c
                         (mv-nth 0
                                 (find-d-e d-e-list filename)))))
           0 nil))
         1))))))
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (place-contents
         (update-fati
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth 0
                     (d-e-cc
                      fat32$c
                      (mv-nth 0
                              (find-d-e d-e-list filename))))
             (make-list-ac
              (len
               (mv-nth 0
                       (d-e-cc
                        fat32$c
                        (mv-nth 0
                                (find-d-e d-e-list filename)))))
              0 nil))
            1))
          (fat32-update-lower-28
           (fati
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth 0
                       (d-e-cc
                        fat32$c
                        (mv-nth 0
                                (find-d-e d-e-list filename))))
               (make-list-ac
                (len
                 (mv-nth 0
                         (d-e-cc
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list filename)))))
                0 nil))
              1))
            fat32$c)
           268435455)
          (mv-nth 0
                  (clear-cc
                   fat32$c
                   (d-e-first-cluster
                    (mv-nth 0 (find-d-e d-e-list filename)))
                   (d-e-file-size
                    (mv-nth 0
                            (find-d-e d-e-list filename))))))
         (mv-nth 0 (find-d-e d-e-list filename))
         (lofat-file->contents file)
         (len (explode (lofat-file->contents file)))
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth 0
                    (d-e-cc
                     fat32$c
                     (mv-nth 0
                             (find-d-e d-e-list filename))))
            (make-list-ac
             (len
              (mv-nth 0
                      (d-e-cc
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename)))))
             0 nil))
           1))))
       (place-d-e
        d-e-list
        (d-e-set-first-cluster-file-size
         (mv-nth 0 (find-d-e d-e-list filename))
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth 0
                    (d-e-cc
                     fat32$c
                     (mv-nth 0
                             (find-d-e d-e-list filename))))
            (make-list-ac
             (len
              (mv-nth 0
                      (d-e-cc
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename)))))
             0 nil))
           1))
         (len (explode (lofat-file->contents file)))))
       entry-limit))
     0)
    (equal
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (place-contents
         (update-fati
          (nth
           0
           (find-n-free-clusters
            (set-indices-in-fa-table
             (effective-fat fat32$c)
             (mv-nth 0
                     (d-e-cc
                      fat32$c
                      (mv-nth 0
                              (find-d-e d-e-list filename))))
             (make-list-ac
              (len
               (mv-nth 0
                       (d-e-cc
                        fat32$c
                        (mv-nth 0
                                (find-d-e d-e-list filename)))))
              0 nil))
            1))
          (fat32-update-lower-28
           (fati
            (nth
             0
             (find-n-free-clusters
              (set-indices-in-fa-table
               (effective-fat fat32$c)
               (mv-nth 0
                       (d-e-cc
                        fat32$c
                        (mv-nth 0
                                (find-d-e d-e-list filename))))
               (make-list-ac
                (len
                 (mv-nth 0
                         (d-e-cc
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list filename)))))
                0 nil))
              1))
            fat32$c)
           268435455)
          (mv-nth 0
                  (clear-cc
                   fat32$c
                   (d-e-first-cluster
                    (mv-nth 0 (find-d-e d-e-list filename)))
                   (d-e-file-size
                    (mv-nth 0
                            (find-d-e d-e-list filename))))))
         (mv-nth 0 (find-d-e d-e-list filename))
         (lofat-file->contents file)
         (len (explode (lofat-file->contents file)))
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth 0
                    (d-e-cc
                     fat32$c
                     (mv-nth 0
                             (find-d-e d-e-list filename))))
            (make-list-ac
             (len
              (mv-nth 0
                      (d-e-cc
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename)))))
             0 nil))
           1))))
       (place-d-e
        d-e-list
        (d-e-set-first-cluster-file-size
         (mv-nth 0 (find-d-e d-e-list filename))
         (nth
          0
          (find-n-free-clusters
           (set-indices-in-fa-table
            (effective-fat fat32$c)
            (mv-nth 0
                    (d-e-cc
                     fat32$c
                     (mv-nth 0
                             (find-d-e d-e-list filename))))
            (make-list-ac
             (len
              (mv-nth 0
                      (d-e-cc
                       fat32$c
                       (mv-nth 0
                               (find-d-e d-e-list filename)))))
             0 nil))
           1))
         (len (explode (lofat-file->contents file)))))
       entry-limit))
     (put-assoc-equal
      filename
      (m1-file
       (d-e-set-first-cluster-file-size
        (mv-nth 0 (find-d-e d-e-list filename))
        (nth
         0
         (find-n-free-clusters
          (set-indices-in-fa-table
           (effective-fat fat32$c)
           (mv-nth 0
                   (d-e-cc
                    fat32$c
                    (mv-nth 0
                            (find-d-e d-e-list filename))))
           (make-list-ac
            (len (mv-nth 0
                         (d-e-cc
                          fat32$c
                          (mv-nth 0
                                  (find-d-e d-e-list filename)))))
            0 nil))
          1))
        (len (explode (lofat-file->contents file))))
       (lofat-file->contents file))
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c
                                     d-e-list entry-limit))))))
  :hints (("goal" :in-theory (e/d
                              (non-free-index-listp)
                              (lofat-place-file-correctness-lemma-30))
           :use (:instance lofat-place-file-correctness-lemma-30
                           (x nil)))))

(defthm
  lofat-place-file-correctness-lemma-31
  (implies
   (and
    (<= *ms-first-data-cluster* i)
    (fat32-masked-entry-p i)
    (zp (fat32-entry-mask (fati i fat32$c)))
    (< i
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32$c)))
    (d-e-p d-e)
    (lofat-fs-p fat32$c)
    (integerp entry-limit)
    (< (mv-nth 1
               (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
       entry-limit)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit))
           0)
    (zp
     (mv-nth
      2
      (place-contents (update-fati i
                                   (fat32-update-lower-28 (fati i fat32$c)
                                                          268435455)
                                   fat32$c)
                      (d-e-install-directory-bit (make-d-e-with-filename name)
                                                 t)
                      (make-empty-subdir-contents i (d-e-first-cluster d-e))
                      0 i)))
    (useful-d-e-list-p d-e-list)
    (fat32-filename-p name))
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth 0
               (place-contents
                (update-fati i
                             (fat32-update-lower-28 (fati i fat32$c)
                                                    268435455)
                             fat32$c)
                (d-e-install-directory-bit (make-d-e-with-filename name)
                                           t)
                (make-empty-subdir-contents i (d-e-first-cluster d-e))
                0 i))
       (place-d-e
        d-e-list
        (d-e-set-first-cluster-file-size
         (d-e-install-directory-bit (make-d-e-with-filename name)
                                    t)
         i 0))
       entry-limit))
     0)
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth 0
               (place-contents
                (update-fati i
                             (fat32-update-lower-28 (fati i fat32$c)
                                                    268435455)
                             fat32$c)
                (d-e-install-directory-bit (make-d-e-with-filename name)
                                           t)
                (make-empty-subdir-contents i (d-e-first-cluster d-e))
                0 i))
       (place-d-e
        d-e-list
        (d-e-set-first-cluster-file-size
         (d-e-install-directory-bit (make-d-e-with-filename name)
                                    t)
         i 0))
       entry-limit))
     (put-assoc-equal
      name
      (m1-file-hifat-file-alist-fix d-e nil)
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))))
  :hints (("goal" :do-not-induct t
           :in-theory
           (e/d (non-free-index-listp)
                (lofat-place-file-correctness-lemma-158))
           :use (:instance lofat-place-file-correctness-lemma-158
                           (x nil)))))

(defthm
  lofat-place-file-correctness-lemma-172
  (implies
   (and
    (lofat-fs-p fat32$c)
    (useful-d-e-list-p d-e-list)
    (fat32-masked-entry-p i)
    (<= *ms-first-data-cluster* i)
    (zp
     (fat32-entry-mask
      (nth
       i
       (effective-fat
        (mv-nth
         0
         (clear-cc fat32$c
                   (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
                   *ms-max-dir-size*))))))
    (zp (mv-nth 3
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
    (< i
       (+ *ms-first-data-cluster*
          (count-of-clusters fat32$c)))
    (zp
     (mv-nth
      2
      (place-contents
       (update-fati
        i
        (fat32-update-lower-28 (fati i fat32$c)
                               268435455)
        (mv-nth
         0
         (clear-cc fat32$c
                   (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
                   *ms-max-dir-size*)))
       (mv-nth 0 (find-d-e d-e-list name))
       (make-empty-subdir-contents i (d-e-first-cluster d-e))
       0 i)))
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
    (d-e-p d-e))
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       (mv-nth
        0
        (place-contents
         (update-fati
          i
          (fat32-update-lower-28 (fati i fat32$c)
                                 268435455)
          (mv-nth
           0
           (clear-cc fat32$c
                     (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
                     *ms-max-dir-size*)))
         (mv-nth 0 (find-d-e d-e-list name))
         (make-empty-subdir-contents i (d-e-first-cluster d-e))
         0 i))
       (place-d-e
        d-e-list
        (d-e-set-first-cluster-file-size (mv-nth 0 (find-d-e d-e-list name))
                                         i 0))
       entry-limit))
     0)
    (not-intersectp-list
     nil
     (mv-nth
      2
      (lofat-to-hifat-helper
       (mv-nth
        0
        (place-contents
         (update-fati
          i
          (fat32-update-lower-28 (fati i fat32$c)
                                 268435455)
          (mv-nth
           0
           (clear-cc fat32$c
                     (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
                     *ms-max-dir-size*)))
         (mv-nth 0 (find-d-e d-e-list name))
         (make-empty-subdir-contents i (d-e-first-cluster d-e))
         0 i))
       (place-d-e
        d-e-list
        (d-e-set-first-cluster-file-size (mv-nth 0 (find-d-e d-e-list name))
                                         i 0))
       entry-limit)))
    (hifat-equiv
     (mv-nth
      0
      (lofat-to-hifat-helper
       (mv-nth
        0
        (place-contents
         (update-fati
          i
          (fat32-update-lower-28 (fati i fat32$c)
                                 268435455)
          (mv-nth
           0
           (clear-cc fat32$c
                     (d-e-first-cluster (mv-nth 0 (find-d-e d-e-list name)))
                     *ms-max-dir-size*)))
         (mv-nth 0 (find-d-e d-e-list name))
         (make-empty-subdir-contents i (d-e-first-cluster d-e))
         0 i))
       (place-d-e
        d-e-list
        (d-e-set-first-cluster-file-size (mv-nth 0 (find-d-e d-e-list name))
                                         i 0))
       entry-limit))
     (put-assoc-equal
      name
      (m1-file-hifat-file-alist-fix d-e nil)
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (non-free-index-listp)
                           (lofat-place-file-correctness-lemma-171))
           :use (:instance lofat-place-file-correctness-lemma-171
                           (x nil)))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  ;; Hypotheses are minimal.
  (make-event
   `(defthm
      make-d-e-list-of-append-4
      (implies
       (and (d-e-p d-e)
            (not (useless-d-e-p d-e))
            (fat32-filename-p (d-e-filename d-e))
            (equal (mod (len (explode dir-contents))
                        *ms-d-e-length*)
                   0))
       (equal
        (make-d-e-list
         (implode
          (append
           (nats=>chars (insert-d-e (string=>nats dir-contents)
                                    d-e))
           (make-list-ac n ,(code-char 0) nil))))
        (place-d-e (make-d-e-list dir-contents)
                   d-e)))
      :hints
      (("goal" :do-not-induct t
        :in-theory
        (e/d (make-d-e-list d-e-fix insert-d-e string=>nats
                            nats=>string fat32-filename-p)))))))

(defthm
  lofat-fs-p-of-lofat-place-file-lemma-3
  (implies (<= 1
               (count-free-clusters (effective-fat fat32$c)))
           (<= *ms-first-data-cluster*
               (nth '0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          '1)))))

(defthm
  lofat-place-file-guard-lemma-3
  (implies
   (<=
    1
    (count-free-clusters
     (set-indices-in-fa-table
      (effective-fat fat32$c)
      (mv-nth
       0
       (d-e-cc
        fat32$c
        (mv-nth
         0
         (find-d-e
          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
          name))))
      (make-list-ac
       (len
        (mv-nth
         0
         (d-e-cc
          fat32$c
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            name)))))
       0 nil))))
   (<=
    2
    (nth
     0
     (find-n-free-clusters
      (set-indices-in-fa-table
       (effective-fat fat32$c)
       (mv-nth
        0
        (d-e-cc
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           name))))
       (make-list-ac
        (len
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
             name)))))
        0 nil))
      1)))))

(defthm
  d-e-cc-contents-of-lofat-place-file-disjoint-lemma-2
  (implies
   (and
    (<=
     2
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 name))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 name)))
     (+ 2 (count-of-clusters fat32$c)))
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (not-intersectp-list
     (mv-nth 0 (d-e-cc fat32$c d-e))
     (mv-nth
      2
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit)))
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0))
   (not
    (member-equal
     (nth
      '0
      (find-n-free-clusters
       (set-indices-in-fa-table
        (effective-fat fat32$c)
        (mv-nth
         '0
         (d-e-cc
          fat32$c
          (mv-nth
           '0
           (find-d-e
            (make-d-e-list (mv-nth '0
                                   (d-e-cc-contents fat32$c root-d-e)))
            name))))
        (make-list-ac
         (len
          (mv-nth
           '0
           (d-e-cc
            fat32$c
            (mv-nth
             '0
             (find-d-e
              (make-d-e-list (mv-nth '0
                                     (d-e-cc-contents fat32$c root-d-e)))
              name)))))
         '0
         'nil))
       '1))
     (mv-nth '0 (d-e-cc fat32$c d-e)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite non-free-index-listp-correctness-2 . 1))
    :use
    ((:instance
      (:rewrite non-free-index-listp-correctness-2 . 1)
      (x (mv-nth 0 (d-e-cc fat32$c d-e)))
      (key
       (nth
        0
        (find-n-free-clusters
         (set-indices-in-fa-table
          (effective-fat fat32$c)
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              name))))
          (make-list-ac
           (len
            (mv-nth
             0
             (d-e-cc
              fat32$c
              (mv-nth
               0
               (find-d-e
                (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                name)))))
           0 nil))
         1)))
      (fa-table
       (set-indices-in-fa-table
        (effective-fat fat32$c)
        (mv-nth
         0
         (d-e-cc
          fat32$c
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            name))))
        (make-list-ac
         (len
          (mv-nth
           0
           (d-e-cc
            fat32$c
            (mv-nth
             0
             (find-d-e
              (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
              name)))))
         0 nil))))))))

(defthm lofat-place-file-correctness-lemma-44
  (implies (and (not (zp (cluster-size fat32$c)))
                (< 0 (length (lofat-file->contents file))))
           (< 0
              (len (make-clusters (lofat-file->contents file)
                                  (cluster-size fat32$c)))))
  :hints (("goal" :in-theory (enable make-clusters)))
  :rule-classes :linear)

(defthm
  lofat-place-file-correctness-lemma-35
  (implies
   (and (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
               0)
        (<= (mv-nth 1
                    (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
            (nfix entry-limit2)))
   (and
    (equal
     (equal
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit2)))
     t)
    (equal
     (equal
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit2))
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c d-e-list entry-limit1)))
     t)))
  :hints (("goal" :do-not-induct t
           :use lofat-to-hifat-helper-correctness-4)))

(defthm
  lofat-place-file-correctness-lemma-37
  (implies
   (and
    (useful-d-e-list-p d-e-list)
    (not (d-e-directory-p (d-e-fix d-e)))
    (zp (mv-nth 3
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
    (or
     (< (d-e-first-cluster (d-e-fix d-e)) 2)
     (<= (+ 2 (count-of-clusters fat32$c))
         (d-e-first-cluster (d-e-fix d-e)))
     (and (equal (mv-nth 1
                         (d-e-cc-contents fat32$c (d-e-fix d-e)))
                 0)
          (not (intersectp-equal x
                                 (mv-nth 0 (d-e-cc fat32$c (d-e-fix d-e)))))))
    (not-intersectp-list
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))
   (not-intersectp-list
    x
    (mv-nth 2
            (lofat-to-hifat-helper fat32$c (place-d-e d-e-list d-e)
                                   entry-limit))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper hifat-entry-count not-intersectp-list)
     ((:rewrite nth-of-effective-fat)
      (:rewrite nth-of-nats=>chars)
      (:linear nth-when-d-e-p)
      (:rewrite explode-of-d-e-filename)
      (:rewrite take-of-len-free)
      (:rewrite
       hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
      (:rewrite put-assoc-equal-without-change . 2)
      (:rewrite nats=>chars-of-take)
      (:rewrite hifat-to-lofat-inversion-lemma-2)
      (:rewrite subsetp-car-member)
      (:rewrite consp-of-assoc-of-hifat-file-alist-fix)
      (:rewrite assoc-of-car-when-member)
      (:rewrite not-intersectp-list-when-atom)
      (:rewrite subdir-contents-p-when-zero-length)
      (:definition binary-append)
      (:rewrite hifat-file-alist-fix-guard-lemma-1)
      (:rewrite not-intersectp-list-when-subsetp-1)
      (:rewrite subsetp-when-atom-left)
      (:rewrite subsetp-trans2)
      (:rewrite subsetp-trans)
      (:rewrite subsetp-append1)
      (:rewrite m1-directory-file-p-when-m1-file-p)))
    :do-not-induct t
    :induct (lofat-to-hifat-helper fat32$c d-e-list entry-limit)
    :expand ((:free (fat32$c d-e d-e-list entry-limit)
                    (lofat-to-hifat-helper fat32$c (cons d-e d-e-list)
                                           entry-limit))
             (:free (x) (intersectp-equal nil x))))))

(defthmd
  lofat-place-file-correctness-lemma-41
  (implies
   (and
    (useful-d-e-list-p d-e-list)
    (not (d-e-directory-p (d-e-fix d-e)))
    (zp (mv-nth 3
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit)))
    (> (nfix entry-limit)
       (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit))))
    (or
     (< (d-e-first-cluster (d-e-fix d-e))
        2)
     (<= (+ 2 (count-of-clusters fat32$c))
         (d-e-first-cluster (d-e-fix d-e)))
     (and
      (equal
       (mv-nth
        1
        (d-e-cc-contents fat32$c (d-e-fix d-e)))
       0)
      (not-intersectp-list
       (mv-nth 0
               (d-e-cc fat32$c (d-e-fix d-e)))
       x)))
    (not (member-intersectp-equal
          x
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c
                                         d-e-list entry-limit)))))
   (not
    (member-intersectp-equal
     x
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c
                                    (place-d-e d-e-list d-e)
                                    entry-limit)))))
  :hints
  (("goal"
    :induct (member-intersectp-equal
             x
             (mv-nth 2
                     (lofat-to-hifat-helper fat32$c
                                            d-e-list entry-limit)))
    :in-theory (enable not-intersectp-list))))

;; Introduce a rewrite rule gingerly...
(defthm
  lofat-place-file-correctness-lemma-43
  (implies (lofat-regular-file-p file)
           (iff (equal (len (explode (lofat-file->contents file)))
                       0)
                (equal (lofat-file->contents file) "")))
  :hints (("goal" :expand (len (explode (lofat-file->contents file))))))

(defthm lofat-place-file-correctness-lemma-45
  (equal (make-clusters "" cluster-size)
         nil)
  :hints (("goal" :in-theory (enable make-clusters))))

(defthm
  lofat-place-file-correctness-lemma-47
  (implies (and (< (d-e-first-cluster root-d-e)
                   (+ 2 (count-of-clusters fat32$c)))
                (<= 1
                    (count-free-clusters (effective-fat fat32$c))))
           (< (nth '0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         '1))
              (binary-+ '2
                        (count-of-clusters fat32$c))))
  :rule-classes (:rewrite :linear))

(defthm
  lofat-place-file-correctness-lemma-59
  (implies
   (and
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
    (useful-d-e-list-p d-e-list)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit1))
           0)
    (<=
     (mv-nth
      1
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents
                 fat32$c
                 (mv-nth 0 (find-d-e d-e-list name)))))
       entry-limit1))
     (nfix entry-limit2)))
   (and
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper
              fat32$c
              (make-d-e-list
               (mv-nth 0
                       (d-e-cc-contents
                        fat32$c
                        (mv-nth 0 (find-d-e d-e-list name)))))
              entry-limit2))
     0)
    (<
     (hifat-entry-count
      (mv-nth
       0
       (lofat-to-hifat-helper
        fat32$c
        (make-d-e-list
         (mv-nth 0
                 (d-e-cc-contents
                  fat32$c
                  (mv-nth 0 (find-d-e d-e-list name)))))
        entry-limit2)))
     entry-limit1)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable lofat-find-file-correctness-1-lemma-6)
    :use
    ((:instance lofat-find-file-correctness-1-lemma-6
                (entry-limit entry-limit1))
     (:instance
      lofat-to-hifat-helper-correctness-4
      (d-e-list
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents
                 fat32$c
                 (mv-nth 0
                         (find-d-e d-e-list name))))))))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name)))
      (useful-d-e-list-p d-e-list)
      (equal (mv-nth 3
                     (lofat-to-hifat-helper fat32$c
                                            d-e-list entry-limit1))
             0)
      (<=
       (mv-nth
        1
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents
                   fat32$c
                   (mv-nth 0 (find-d-e d-e-list name)))))
         entry-limit1))
       (nfix entry-limit2)))
     (equal
      (mv-nth 3
              (lofat-to-hifat-helper
               fat32$c
               (make-d-e-list
                (mv-nth 0
                        (d-e-cc-contents
                         fat32$c
                         (mv-nth 0 (find-d-e d-e-list name)))))
               entry-limit2))
      0)))))

(defthm
  lofat-place-file-correctness-lemma-49
  (implies
   (and
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit1))
     0)
    (<=
     (mv-nth 1
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit1))
     (nfix entry-limit2)))
   (equal
    (hifat-equiv
     (cons
      x
      (mv-nth
       0
       (lofat-to-hifat-helper fat32$c
                              d-e-list entry-limit2)))
     (cons
      x
      (mv-nth
       0
       (lofat-to-hifat-helper fat32$c
                              d-e-list entry-limit1))))
    t))
  :hints
  (("goal"
    :in-theory (disable lofat-to-hifat-helper-correctness-4)
    :use lofat-to-hifat-helper-correctness-4)))

(defthm
  lofat-place-file-correctness-lemma-54
  (implies
   (and (natp entry-limit)
        (useful-d-e-list-p d-e-list))
   (not
    (< entry-limit
       (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper
                 fat32$c
                 d-e-list (+ -1 entry-limit)))))))
  :instructions
  (:promote (:dv 1)
            (:apply-linear lofat-to-hifat-helper-correctness-3)
            :top (:bash ("Goal" :in-theory (enable nfix))))
  :rule-classes :linear)

(defthm
  lofat-place-file-correctness-lemma-93
  (implies
   (and
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit1))
     0)
    (not
     (member-intersectp-equal
      (mv-nth 2
              (lofat-to-hifat-helper fat32$c
                                     d-e-list entry-limit1))
      y))
    (<=
     (mv-nth 1
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit1))
     (nfix entry-limit2)))
   (not
    (member-intersectp-equal
     (mv-nth 2
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit2))
     y)))
  :hints
  (("goal"
    :in-theory (disable lofat-to-hifat-helper-correctness-4)
    :use lofat-to-hifat-helper-correctness-4)))

(defthm
  lofat-place-file-correctness-lemma-62
  (implies
   (and
    (not
     (member-intersectp-equal
      (set-difference-equal
       x
       (mv-nth 2
               (lofat-to-hifat-helper fat32$c1
                                      d-e-list1 entry-limit1)))
      (mv-nth 2
              (lofat-to-hifat-helper fat32$c2
                                     d-e-list2 entry-limit1))))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c1
                                          d-e-list1 entry-limit1))
           0)
    (>= (nfix entry-limit2)
        (mv-nth 1
                (lofat-to-hifat-helper fat32$c1
                                       d-e-list1 entry-limit1)))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c2
                                          d-e-list2 entry-limit1))
           0)
    (>= (nfix entry-limit2)
        (mv-nth 1
                (lofat-to-hifat-helper fat32$c2
                                       d-e-list2 entry-limit1))))
   (not (member-intersectp-equal
         (set-difference-equal
          x
          (mv-nth 2
                  (lofat-to-hifat-helper fat32$c1
                                         d-e-list1 entry-limit2)))
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c2
                                        d-e-list2 entry-limit2)))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable lofat-to-hifat-helper-correctness-4)
           :use ((:instance lofat-to-hifat-helper-correctness-4
                            (fat32$c fat32$c1)
                            (d-e-list d-e-list1))
                 (:instance lofat-to-hifat-helper-correctness-4
                            (fat32$c fat32$c2)
                            (d-e-list d-e-list2))))))

(defthm
  lofat-place-file-correctness-lemma-48
  (implies
   (and
    (d-e-directory-p (mv-nth 0
                             (find-d-e d-e-list name)))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list
                                          entry-limit1))
           0)
    (>= (nfix entry-limit2)
        (mv-nth 1
                (lofat-to-hifat-helper
                 fat32$c
                 (make-d-e-list
                  (mv-nth 0
                          (d-e-cc-contents
                           fat32$c
                           (mv-nth 0
                                   (find-d-e d-e-list
                                             name)))))
                 entry-limit1)))
    (useful-d-e-list-p d-e-list))
   (equal
    (hifat-equiv
     (mv-nth
      0
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents
                   fat32$c
                   (mv-nth 0
                           (find-d-e d-e-list
                                     name)))))
         entry-limit2))
       path file))
     (mv-nth
      0
      (hifat-place-file
       (mv-nth
        0
        (lofat-to-hifat-helper
         fat32$c
         (make-d-e-list
          (mv-nth 0
                  (d-e-cc-contents
                   fat32$c
                   (mv-nth 0
                           (find-d-e d-e-list
                                     name)))))
         entry-limit1))
       path file)))
    t))
  :hints
  (("goal"
    :use
    (:instance
     lofat-to-hifat-helper-correctness-4
     (d-e-list
      (make-d-e-list (mv-nth 0
                             (d-e-cc-contents
                              fat32$c
                              (mv-nth 0
                                      (find-d-e d-e-list
                                                name))))))
     (fat32$c fat32$c)))))

(defthm
  lofat-place-file-correctness-lemma-95
  (implies
   (and
    (hifat-equiv
     y
     (put-assoc-equal
      name
      (m1-file-hifat-file-alist-fix
       (mv-nth 0 (find-d-e d-e-list2 name))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth
          0
          (lofat-to-hifat-helper
           fat32$c
           (make-d-e-list
            (mv-nth 0
                    (d-e-cc-contents
                     fat32$c
                     (mv-nth 0 (find-d-e d-e-list2 name)))))
           entry-limit1))
         path
         (m1-file-hifat-file-alist-fix d-e nil))))
      (mv-nth 0
              (lofat-to-hifat-helper fat32$c
                                     d-e-list2 entry-limit1))))
    (<=
     (mv-nth
      1
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list
        (mv-nth 0
                (d-e-cc-contents
                 fat32$c
                 (mv-nth 0 (find-d-e d-e-list2 name)))))
       entry-limit1))
     (nfix entry-limit2))
    (d-e-directory-p (mv-nth 0 (find-d-e d-e-list2 name)))
    (useful-d-e-list-p d-e-list2)
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list2 entry-limit1))
           0))
   (equal
    (hifat-equiv
     (cons x y)
     (cons
      x
      (put-assoc-equal
       name
       (m1-file-hifat-file-alist-fix
        (mv-nth 0 (find-d-e d-e-list2 name))
        (mv-nth
         0
         (hifat-place-file
          (mv-nth
           0
           (lofat-to-hifat-helper
            fat32$c
            (make-d-e-list
             (mv-nth 0
                     (d-e-cc-contents
                      fat32$c
                      (mv-nth 0 (find-d-e d-e-list2 name)))))
            entry-limit2))
          path
          (m1-file-hifat-file-alist-fix d-e nil))))
       (mv-nth 0
               (lofat-to-hifat-helper fat32$c
                                      d-e-list2 entry-limit1)))))
    t))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance
     lofat-to-hifat-helper-correctness-4
     (entry-limit2 entry-limit2)
     (d-e-list
      (make-d-e-list
       (mv-nth 0
               (d-e-cc-contents
                fat32$c
                (mv-nth 0 (find-d-e d-e-list2 name))))))
     (fat32$c fat32$c)))))

(defthm
  lofat-place-file-correctness-lemma-63
  (<
   (binary-*
    (cluster-size fat32$c)
    (len
     (cdr (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32$c)
                                          (d-e-first-cluster d-e)
                                          2097152 (cluster-size fat32$c))))))
   2097152)
  :hints
  (("goal" :in-theory (enable place-contents-correctness-1
                              d-e-cc fat32-build-index-list)
    :use (:instance (:linear len-of-fat32-build-index-list-1 . 3)
                    (length 2097152)
                    (masked-current-cluster (d-e-first-cluster d-e))
                    (fa-table (effective-fat fat32$c))
                    (cluster-size (cluster-size fat32$c)))))
  :rule-classes :linear)

(local
 (defthm
   lofat-place-file-correctness-lemma-122
   (implies
    (consp
     (mv-nth 0
             (fat32-build-index-list (effective-fat fat32$c)
                                     (d-e-first-cluster d-e)
                                     2097152 (cluster-size fat32$c))))
    (equal
     (car (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32$c)
                                          (d-e-first-cluster d-e)
                                          2097152 (cluster-size fat32$c))))
     (d-e-first-cluster d-e)))
   :hints
   (("goal" :do-not-induct t
     :expand (fat32-build-index-list (effective-fat fat32$c)
                                     (d-e-first-cluster d-e)
                                     2097152 (cluster-size fat32$c))))))

(defthm
  lofat-place-file-correctness-lemma-127
  (implies
   (and (d-e-directory-p d-e)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (< 0 (cluster-size fat32$c)))
   (equal
    (d-e-cc (update-fati
             (d-e-first-cluster d-e)
             (fat32-update-lower-28 (fati (d-e-first-cluster d-e) fat32$c)
                                    268435455)
             (mv-nth 0
                     (clear-cc fat32$c (d-e-first-cluster d-e)
                               2097152)))
            d-e)
    (mv (list (d-e-first-cluster d-e)) 0)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable d-e-cc fat32-build-index-list))))

(defthm
  lofat-place-file-correctness-lemma-67
  (implies
   (and
    (consp
     (cdr (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32$c)
                                          (d-e-first-cluster d-e)
                                          2097152 (cluster-size fat32$c)))))
    (lofat-fs-p fat32$c)
    (d-e-directory-p d-e)
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0))
   (<=
    (+ 2 (count-of-clusters fat32$c))
    (fat32-entry-mask
     (fati
      (car
       (last
        (cdr
         (mv-nth 0
                 (fat32-build-index-list (effective-fat fat32$c)
                                         (d-e-first-cluster d-e)
                                         2097152 (cluster-size fat32$c))))))
      fat32$c))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (d-e-cc d-e-cc-contents fat32-build-index-list)
                    (lofat-place-file-correctness-lemma-123))
    :use (:instance (:linear lofat-place-file-correctness-lemma-123)
                    (length 2097152)
                    (masked-current-cluster (d-e-first-cluster d-e))
                    (fat32$c fat32$c))))
  :rule-classes :linear)

(defthm
  lofat-place-file-correctness-lemma-69
  (implies
   (and
    (lofat-fs-p fat32$c)
    (d-e-p d-e)
    (d-e-directory-p d-e)
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0)
    (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c d-e)))
    (not (intersectp-equal x (mv-nth 0 (d-e-cc fat32$c d-e))))
    (< 0 (cluster-size fat32$c))
    (stringp dir-contents)
    (consp
     (cdr (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32$c)
                                          (d-e-first-cluster d-e)
                                          2097152 (cluster-size fat32$c))))))
   (not
    (intersectp-equal
     x
     (mv-nth
      0
      (d-e-cc
       (stobj-set-indices-in-fa-table
        (mv-nth
         0
         (place-contents
          (update-fati
           (d-e-first-cluster d-e)
           (fat32-update-lower-28 (fati (d-e-first-cluster d-e) fat32$c)
                                  268435455)
           (mv-nth 0
                   (clear-cc fat32$c (d-e-first-cluster d-e)
                             2097152)))
          '(0 0 0 0 0 0 0 0 0 0 0 0
              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          dir-contents 0 (d-e-first-cluster d-e)))
        (mv-nth 0
                (fat32-build-index-list (effective-fat fat32$c)
                                        (d-e-first-cluster d-e)
                                        2097152 (cluster-size fat32$c)))
        (append
         (cdr
          (mv-nth 0
                  (fat32-build-index-list (effective-fat fat32$c)
                                          (d-e-first-cluster d-e)
                                          2097152 (cluster-size fat32$c))))
         (list
          (fat32-entry-mask
           (fati
            (car
             (last
              (cdr
               (mv-nth
                0
                (fat32-build-index-list (effective-fat fat32$c)
                                        (d-e-first-cluster d-e)
                                        2097152 (cluster-size fat32$c))))))
            fat32$c)))))
       d-e)))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable d-e-cc))))

(defthm
  lofat-place-file-correctness-lemma-109
  (implies
   (and
    (lofat-fs-p fat32$c)
    (d-e-directory-p d-e)
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0)
    (not
     (intersectp-equal
      x
      (mv-nth 0
              (fat32-build-index-list (effective-fat fat32$c)
                                      (d-e-first-cluster d-e)
                                      2097152 (cluster-size fat32$c)))))
    (not
     (consp
      (cdr (mv-nth 0
                   (fat32-build-index-list (effective-fat fat32$c)
                                           (d-e-first-cluster d-e)
                                           2097152 (cluster-size fat32$c)))))))
   (not
    (intersectp-equal
     x
     (mv-nth
      0
      (fat32-build-index-list
       (set-indices-in-fa-table
        (effective-fat
         (mv-nth
          0
          (place-contents
           (update-fati
            (d-e-first-cluster d-e)
            (fat32-update-lower-28 (fati (d-e-first-cluster d-e) fat32$c)
                                   268435455)
            (mv-nth 0
                    (clear-cc fat32$c (d-e-first-cluster d-e)
                              2097152)))
           '(0 0 0 0 0 0 0 0 0 0 0 0
               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           dir-contents
           0 (d-e-first-cluster d-e))))
        (mv-nth 0
                (fat32-build-index-list (effective-fat fat32$c)
                                        (d-e-first-cluster d-e)
                                        2097152 (cluster-size fat32$c)))
        (list (fat32-entry-mask (fati (d-e-first-cluster d-e)
                                      fat32$c))))
       (d-e-first-cluster d-e)
       2097152 (cluster-size fat32$c))))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (enable d-e-cc fat32-build-index-list
                       d-e-cc-contents get-cc-contents)
    :expand (fat32-build-index-list (effective-fat fat32$c)
                                    (d-e-first-cluster d-e)
                                    2097152 (cluster-size fat32$c)))))

(defthm
  lofat-place-file-correctness-lemma-111
  (implies
   (and
    (lofat-fs-p fat32$c)
    (d-e-directory-p d-e)
    (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
           0)
    (not (intersectp-equal x (mv-nth 0 (d-e-cc fat32$c d-e))))
    (< 0 (cluster-size fat32$c))
    (stringp dir-contents)
    (not
     (consp
      (cdr
       (mv-nth 0
               (fat32-build-index-list (effective-fat fat32$c)
                                       (d-e-first-cluster d-e)
                                       2097152 (cluster-size fat32$c)))))))
   (not
    (intersectp-equal
     x
     (mv-nth
      0
      (d-e-cc
       (stobj-set-indices-in-fa-table
        (mv-nth
         0
         (place-contents
          (update-fati
           (d-e-first-cluster d-e)
           (fat32-update-lower-28 (fati (d-e-first-cluster d-e) fat32$c)
                                  268435455)
           (mv-nth 0
                   (clear-cc fat32$c (d-e-first-cluster d-e)
                             2097152)))
          '(0 0 0 0 0 0 0 0 0 0 0 0
              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          dir-contents 0 (d-e-first-cluster d-e)))
        (mv-nth 0
                (fat32-build-index-list (effective-fat fat32$c)
                                        (d-e-first-cluster d-e)
                                        2097152 (cluster-size fat32$c)))
        (list (fat32-entry-mask (fati (d-e-first-cluster d-e)
                                      fat32$c))))
       d-e)))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable d-e-cc fat32-build-index-list))))

(defthmd
  lofat-place-file-correctness-lemma-15
  (implies
   (and (lofat-fs-p fat32$c)
        (non-free-index-listp x (effective-fat fat32$c))
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c d-e)))
        (not (intersectp-equal (mv-nth 0 (d-e-cc fat32$c d-e))
                               x))
        (<= (length dir-contents) 2097152)
        (stringp dir-contents))
   (not
    (intersectp-equal
     (mv-nth
      0
      (d-e-cc (mv-nth 0
                      (update-dir-contents fat32$c (d-e-first-cluster d-e)
                                           dir-contents))
              d-e))
     x)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (enable update-dir-contents)
    :expand
    (:with
     stobj-set-indices-in-fa-table-correctness-1
     (effective-fat
      (stobj-set-indices-in-fa-table
       (update-fati
        (d-e-first-cluster d-e)
        (fat32-update-lower-28 (fati (d-e-first-cluster d-e) fat32$c)
                               268435455)
        (mv-nth 0
                (clear-cc fat32$c (d-e-first-cluster d-e)
                          2097152)))
       (mv-nth 0
               (fat32-build-index-list (effective-fat fat32$c)
                                       (d-e-first-cluster d-e)
                                       2097152 (cluster-size fat32$c)))
       (binary-append
        (cdr (mv-nth 0
                     (fat32-build-index-list (effective-fat fat32$c)
                                             (d-e-first-cluster d-e)
                                             2097152 (cluster-size fat32$c))))
        (list
         (fat32-entry-mask
          (fati
           (car
            (last
             (cdr
              (mv-nth
               0
               (fat32-build-index-list (effective-fat fat32$c)
                                       (d-e-first-cluster d-e)
                                       2097152 (cluster-size fat32$c))))))
           fat32$c)))))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (lofat-fs-p fat32$c)
          (non-free-index-listp x (effective-fat fat32$c))
          (d-e-p d-e)
          (d-e-directory-p d-e)
          (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
                 0)
          (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c d-e)))
          (not (intersectp-equal (mv-nth 0 (d-e-cc fat32$c d-e))
                                 x))
          (<= (length dir-contents) 2097152)
          (stringp dir-contents))
     (not
      (intersectp-equal
       x
       (mv-nth
        0
        (d-e-cc (mv-nth 0
                        (update-dir-contents fat32$c (d-e-first-cluster d-e)
                                             dir-contents))
                d-e))))))))

(defthm
  lofat-place-file-correctness-lemma-112
  (implies
   (and (lofat-fs-p fat32$c)
        (non-free-index-list-listp l (effective-fat fat32$c))
        (d-e-p d-e)
        (d-e-directory-p d-e)
        (equal (mv-nth 1 (d-e-cc-contents fat32$c d-e))
               0)
        (no-duplicatesp-equal (mv-nth 0 (d-e-cc fat32$c d-e)))
        (not-intersectp-list (mv-nth 0 (d-e-cc fat32$c d-e))
                             l)
        (<= (length dir-contents) 2097152)
        (stringp dir-contents))
   (not-intersectp-list
    (mv-nth
     0
     (d-e-cc (mv-nth 0
                     (update-dir-contents fat32$c (d-e-first-cluster d-e)
                                          dir-contents))
             d-e))
    l))
  :hints
  (("goal"
    :in-theory (enable not-intersectp-list lofat-place-file-correctness-lemma-15))))

(defthm
  lofat-place-file-correctness-lemma-72
  (implies
   (stringp dir-contents)
   (subdir-contents-p
    (implode$inline (nats=>chars (insert-d-e (string=>nats dir-contents)
                                             d-e)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d
     (insert-d-e remove1-d-e
                 subdir-contents-p len-when-d-e-p))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (stringp dir-contents)
     (subdir-contents-p
      (nats=>string (insert-d-e (string=>nats dir-contents)
                                d-e))))
    :hints (("Goal" :in-theory (enable nats=>string))))))

(encapsulate
  ()

  (local (include-book "rtl/rel9/arithmetic/top" :dir :system))

  (defthm lofat-place-file-correctness-lemma-73
    (implies (and (integerp x) (equal (mod x 32) 0))
             (equal (mod (binary-+ x (binary-* 32 (len y)))
                         32)
                    0)))

  (defthm lofat-place-file-correctness-lemma-79
    (implies (and (lofat-fs-p fat32$c)
                  (integerp w)
                  (equal (mod w 32) 0))
             (equal (mod (+ w (- (* 32 (len y)))
                            (* (cluster-size fat32$c) (len z)))
                         32)
                    0))))

(defthm
  lofat-place-file-correctness-lemma-80
  (implies
   (lofat-fs-p fat32$c)
   (equal
    (len (make-clusters (make-empty-subdir-contents current-dir-first-cluster
                                                    parent-dir-first-cluster)
                        (cluster-size fat32$c)))
    1))
  :hints (("goal" :do-not-induct t
           :in-theory (enable make-empty-subdir-contents
                              len-when-d-e-p make-clusters)
           :expand (:free (x y)
                          (make-clusters (nats=>string (append x y))
                                         (cluster-size fat32$c))))))

(defthm
  lofat-place-file-correctness-lemma-81
  (implies
   (and (lofat-fs-p fat32$c)
        (> (fat-entry-count fat32$c) i))
   (equal
    (mv-nth
     2
     (place-contents
      (update-fati i
                   (fat32-update-lower-28 (fati i fat32$c)
                                          268435455)
                   fat32$c)
      (d-e-install-directory-bit (make-d-e-with-filename name)
                                 t)
      (make-empty-subdir-contents i (d-e-first-cluster d-e))
      0 i))
    0))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable d-e-cc-of-update-dir-contents-coincident))))

(defthm
  lofat-place-file-correctness-lemma-82
  (implies
   (and
    (hifat-equiv
     y
     (put-assoc-equal
      name
      (m1-file-hifat-file-alist-fix
       d-e2
       (mv-nth
        0
        (hifat-place-file
         (mv-nth 0
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
         path
         (m1-file d-e (lofat-file->contents file)))))
      fs))
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))
           0)
    (>= (nfix entry-limit2)
        (mv-nth 1
                (lofat-to-hifat-helper fat32$c d-e-list entry-limit1))))
   (hifat-equiv
    (cons
     x
     (put-assoc-equal
      name
      (m1-file-hifat-file-alist-fix
       d-e2
       (mv-nth
        0
        (hifat-place-file
         (mv-nth 0
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit2))
         path
         (m1-file d-e (lofat-file->contents file)))))
      fs))
    (cons x y)))
  :hints (("goal" :do-not-induct t
           :use lofat-to-hifat-helper-correctness-4)))

(defthm
  lofat-place-file-correctness-lemma-13
  (implies
   (and (good-root-d-e-p root-d-e fat32$c)
        (lofat-file-p file)
        (<= (len (make-clusters (lofat-file->contents file)
                                (cluster-size fat32$c)))
            (count-free-clusters (effective-fat fat32$c)))
        (not (lofat-directory-file-p file))
        (< 0
           (len (explode (lofat-file->contents file)))))
   (equal
    (d-e-cc
     (mv-nth
      0
      (place-contents
       (update-fati
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        (fat32-update-lower-28
         (fati (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))
               fat32$c)
         268435455)
        fat32$c)
       (d-e-install-directory-bit
        (d-e-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          name)
        nil)
       (lofat-file->contents file)
       (len (explode (lofat-file->contents file)))
       (nth 0
            (find-n-free-clusters (effective-fat fat32$c)
                                  1))))
     (d-e-set-first-cluster-file-size
      (d-e-install-directory-bit
       (d-e-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                         name)
       nil)
      (nth 0
           (find-n-free-clusters (effective-fat fat32$c)
                                 1))
      (len (explode (lofat-file->contents file)))))
    (mv
     (cons
      (nth 0
           (find-n-free-clusters (effective-fat fat32$c)
                                 1))
      (find-n-free-clusters
       (update-nth
        (nth 0
             (find-n-free-clusters (effective-fat fat32$c)
                                   1))
        (fat32-update-lower-28
         (fati (nth 0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          1))
               fat32$c)
         268435455)
        (effective-fat fat32$c))
       (+ -1
          (len (make-clusters (lofat-file->contents file)
                              (cluster-size fat32$c))))))
     0)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (hifat-place-file (:rewrite lofat-to-hifat-inversion-lemma-4)
                           hifat-find-file)
         ((:definition find-d-e)
          (:definition place-d-e)
          (:rewrite d-e-p-when-member-equal-of-d-e-list-p)
          (:rewrite lofat-fs-p-of-lofat-place-file-lemma-1)
          (:rewrite clear-cc-reversibility-lemma-1)
          (:rewrite d-e-cc-of-place-contents-coincident-2)))
    :restrict ((put-assoc-under-hifat-equiv-3 ((file2 (m1-file d-e "")))))
    :use
    (:instance
     (:rewrite d-e-cc-of-place-contents-coincident-2)
     (d-e1
      (d-e-set-first-cluster-file-size
       (d-e-install-directory-bit
        (d-e-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          name)
        nil)
       (nth 0
            (find-n-free-clusters (effective-fat fat32$c)
                                  1))
       (len (explode (lofat-file->contents file)))))
     (first-cluster (nth 0
                         (find-n-free-clusters (effective-fat fat32$c)
                                               1)))
     (file-length (len (explode (lofat-file->contents file))))
     (contents (lofat-file->contents file))
     (d-e2 (d-e-install-directory-bit
            (d-e-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                              name)
            nil))
     (fat32$c
      (update-fati
       (nth 0
            (find-n-free-clusters (effective-fat fat32$c)
                                  1))
       (fat32-update-lower-28
        (fati (nth 0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         1))
              fat32$c)
        268435455)
       fat32$c))))))

(defthm
  lofat-place-file-correctness-lemma-14
  (implies
   (and (good-root-d-e-p root-d-e fat32$c)
        (lofat-file-p file)
        (<= (len (make-clusters (lofat-file->contents file)
                                (cluster-size fat32$c)))
            (count-free-clusters (effective-fat fat32$c)))
        (not (lofat-directory-file-p file))
        (< 0
           (len (explode (lofat-file->contents file)))))
   (equal
    (d-e-cc-contents
     (mv-nth
      '0
      (place-contents
       (update-fati
        (nth '0
             (find-n-free-clusters (effective-fat fat32$c)
                                   '1))
        (fat32-update-lower-28
         (fati (nth '0
                    (find-n-free-clusters (effective-fat fat32$c)
                                          '1))
               fat32$c)
         '268435455)
        fat32$c)
       (d-e-install-directory-bit
        (d-e-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          name)
        'nil)
       (lofat-file->contents$inline file)
       (len (explode$inline (lofat-file->contents$inline file)))
       (nth '0
            (find-n-free-clusters (effective-fat fat32$c)
                                  '1))))
     (d-e-set-first-cluster-file-size
      (d-e-install-directory-bit
       (d-e-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                             0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                         name)
       'nil)
      (nth '0
           (find-n-free-clusters (effective-fat fat32$c)
                                 '1))
      (len (explode$inline (lofat-file->contents$inline file)))))
    (mv
     (implode
      (append
       (explode (lofat-file->contents file))
       (make-list (+ (- (len (explode (lofat-file->contents file))))
                     (min (len (explode (lofat-file->contents file)))
                          (* (cluster-size fat32$c)
                             (len (make-clusters (lofat-file->contents file)
                                                 (cluster-size fat32$c))))))
                  :initial-element (code-char 0))))
     0)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable (:rewrite d-e-cc-contents-of-place-contents-coincident-2))
    :use
    (:instance
     (:rewrite d-e-cc-contents-of-place-contents-coincident-2)
     (d-e2
      (d-e-set-first-cluster-file-size
       (d-e-install-directory-bit
        (d-e-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                          name)
        nil)
       (nth 0
            (find-n-free-clusters (effective-fat fat32$c)
                                  1))
       (len (explode (lofat-file->contents file)))))
     (first-cluster (nth 0
                         (find-n-free-clusters (effective-fat fat32$c)
                                               1)))
     (file-length (len (explode (lofat-file->contents file))))
     (contents (lofat-file->contents file))
     (d-e1 (d-e-install-directory-bit
            (d-e-set-filename '(0 0 0 0 0 0 0 0 0 0 0 0
                                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                              name)
            nil))
     (fat32$c
      (update-fati
       (nth 0
            (find-n-free-clusters (effective-fat fat32$c)
                                  1))
       (fat32-update-lower-28
        (fati (nth 0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         1))
              fat32$c)
        268435455)
       fat32$c))))))

(defthm lofat-place-file-correctness-lemma-19
  (implies (fat32-filename-p name)
           (not (useless-d-e-p (make-d-e-with-filename name))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable make-d-e-with-filename))))

(defthm lofat-place-file-correctness-lemma-20
  (implies (and (equal (m1-file->contents file1) nil)
                (equal (m1-file->contents file2) nil))
           (equal (hifat-equiv (put-assoc-equal name file1 fs)
                               (put-assoc-equal name file2 fs))
                  t))
  :hints (("goal" :in-theory (e/d (m1-directory-file-p) nil)
           :do-not-induct t
           :restrict (((:rewrite put-assoc-under-hifat-equiv-1)
                       ((file1 file2) (file2 file1)))))))

(defthm
  lofat-place-file-correctness-lemma-23
  (implies
   (and (good-root-d-e-p root-d-e fat32$c)
        (<= (len (make-clusters (lofat-file->contents file)
                                (cluster-size fat32$c)))
            (count-free-clusters (effective-fat fat32$c)))
        (< 0
           (len (explode (lofat-file->contents file)))))
   (equal
    (mv-nth
     '2
     (place-contents
      (update-fati
       (nth '0
            (find-n-free-clusters (effective-fat fat32$c)
                                  '1))
       (fat32-update-lower-28
        (fati (nth '0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         '1))
              fat32$c)
        '268435455)
       fat32$c)
      (d-e-install-directory-bit (make-d-e-with-filename name)
                                 'nil)
      (lofat-file->contents$inline file)
      (len (explode$inline (lofat-file->contents$inline file)))
      (nth '0
           (find-n-free-clusters (effective-fat fat32$c)
                                 '1))))
    '0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite place-contents-expansion-2))
    :use
    (:instance
     (:rewrite place-contents-expansion-2)
     (first-cluster (nth 0
                         (find-n-free-clusters (effective-fat fat32$c)
                                               1)))
     (file-length (len (explode (lofat-file->contents file))))
     (contents (lofat-file->contents file))
     (d-e (d-e-install-directory-bit (make-d-e-with-filename name)
                                     nil))
     (fat32$c
      (update-fati
       (nth 0
            (find-n-free-clusters (effective-fat fat32$c)
                                  1))
       (fat32-update-lower-28
        (fati (nth 0
                   (find-n-free-clusters (effective-fat fat32$c)
                                         1))
              fat32$c)
        268435455)
       fat32$c))))))

(defthm
  lofat-place-file-correctness-lemma-26
  (implies
   (and
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (<=
     2
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 name))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 name)))
     (+ 2 (count-of-clusters fat32$c))))
   (<
    0
    (min
     (binary-+
      (count-free-clusters (effective-fat fat32$c))
      (len
       (mv-nth
        0
        (d-e-cc
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           name))))))
     1)))
  :hints (("goal" :do-not-induct t))
  :rule-classes :linear)

(defthm
  lofat-place-file-correctness-lemma-27
  (implies (and (equal (m1-file->contents file1)
                       (m1-file->contents (cdr (assoc-equal name fs))))
                (m1-regular-file-p (m1-file-fix file1))
                (m1-regular-file-p (m1-file-fix (cdr (assoc-equal name fs))))
                (consp (assoc-equal name fs)))
           (hifat-equiv (put-assoc-equal name file1 fs)
                        fs))
  :hints
  (("goal" :in-theory (e/d ((:rewrite put-assoc-equal-without-change . 2))
                           (put-assoc-under-hifat-equiv-3))
    :use (:instance put-assoc-under-hifat-equiv-3
                    (file2 (cdr (assoc-equal name fs))))
    :do-not-induct t)))

(defthm
  lofat-place-file-correctness-lemma-28
  (implies
   (lofat-regular-file-p file)
   (not (m1-file-alist-p (lofat-file->contents file))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (lofat-regular-file-p)))))

(defthm
  lofat-place-file-correctness-lemma-39
  (implies
   (and
    (good-root-d-e-p root-d-e fat32$c)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (<=
     2
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 name))))
    (<
     (d-e-first-cluster
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 name)))
     (+ 2 (count-of-clusters fat32$c)))
    (not
     (member-equal
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32$c)
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
             name))))
         (make-list-ac
          (len
           (mv-nth
            0
            (d-e-cc
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               name)))))
          0 nil))
        1))
      (mv-nth
       0
       (d-e-cc
        fat32$c
        (mv-nth
         0
         (find-d-e
          (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
          name)))))))
   (equal
    (fat32-entry-mask
     (fati
      (nth
       0
       (find-n-free-clusters
        (set-indices-in-fa-table
         (effective-fat fat32$c)
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
             name))))
         (make-list-ac
          (len
           (mv-nth
            0
            (d-e-cc
             fat32$c
             (mv-nth
              0
              (find-d-e
               (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               name)))))
          0 nil))
        1))
      fat32$c))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite find-n-free-clusters-correctness-5))
    :use
    (:instance
     (:rewrite find-n-free-clusters-correctness-5)
     (n1 1)
     (fa-table
      (set-indices-in-fa-table
       (effective-fat fat32$c)
       (mv-nth
        0
        (d-e-cc
         fat32$c
         (mv-nth
          0
          (find-d-e
           (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
           name))))
       (make-list-ac
        (len
         (mv-nth
          0
          (d-e-cc
           fat32$c
           (mv-nth
            0
            (find-d-e
             (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
             name)))))
        0 nil)))
     (n2 0)))))

(defthm
  lofat-place-file-correctness-lemma-52
  (implies
   (and
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit1))
     0)
    (subsetp-equal
     (mv-nth
      2
      (lofat-to-hifat-helper fat32$c
                             d-e-list entry-limit1))
     y)
    (>=
     (nfix entry-limit2)
     (mv-nth 1
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit1))))
   (subsetp-equal
    (mv-nth 2
            (lofat-to-hifat-helper fat32$c
                                   d-e-list entry-limit2))
    y))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable lofat-to-hifat-helper-correctness-4)
    :use lofat-to-hifat-helper-correctness-4)))

(defthm
  lofat-place-file-correctness-lemma-61
  (implies
   (and (equal (mv-nth 3
                       (lofat-to-hifat-helper fat32$c
                                              d-e-list entry-limit))
               0)
        (useful-d-e-list-p d-e-list)
        ;; This hypothesis might be removable.
        (d-e-directory-p (mv-nth 0 (find-d-e d-e-list name))))
   (subsetp-equal
    (mv-nth
     2
     (lofat-to-hifat-helper
      fat32$c
      (make-d-e-list
       (mv-nth 0
               (d-e-cc-contents
                fat32$c
                (mv-nth 0 (find-d-e d-e-list name)))))
      entry-limit))
    (mv-nth 2
            (lofat-to-hifat-helper fat32$c
                                   d-e-list entry-limit))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (find-d-e lofat-to-hifat-helper hifat-entry-count
               lofat-to-hifat-helper-correctness-4)
     ((:rewrite nth-of-effective-fat)
      (:rewrite nth-of-nats=>chars)
      (:linear nth-when-d-e-p)
      (:rewrite nfix-when-zp)
      (:rewrite explode-of-d-e-filename)
      (:rewrite
       hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
      (:rewrite d-e-p-when-member-equal-of-d-e-list-p))))))

(defthm
  lofat-place-file-correctness-lemma-98
  (implies
   (and (lofat-fs-p fat32$c)
        (> (fat-entry-count fat32$c) i))
   (equal
    (mv-nth
     2
     (place-contents
      (update-fati
       i
       (fat32-update-lower-28 (fati i fat32$c)
                              268435455)
       (mv-nth
        0
        (clear-cc
         fat32$c
         (d-e-first-cluster
          (mv-nth
           0
           (find-d-e
            (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
            name)))
         2097152)))
      (mv-nth
       0
       (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                 name))
      (make-empty-subdir-contents i (d-e-first-cluster root-d-e))
      0 i))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable (:rewrite d-e-cc-contents-of-lofat-remove-file-disjoint-lemma-7
                       . 5)))))

(defund stobj-disjoins-list
  (fat32$c d-e-list entry-limit x)
  (declare (xargs :stobjs fat32$c :verify-guards nil))
  (b*
      (((mv & & cc-list error-code)
        (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))
    (and (zp error-code)
         (not-intersectp-list x cc-list))))

(defthm
  lofat-place-file-correctness-lemma-68
  (implies
   (and (consp x)
        (not-intersectp-list
         x
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit))))
   (not (member-equal
         x
         (mv-nth 2
                 (lofat-to-hifat-helper fat32$c d-e-list entry-limit)))))
  :hints
  (("goal"
    :in-theory
    (e/d
     (lofat-to-hifat-helper not-intersectp-list find-d-e)
     ((:rewrite nfix-when-zp)
      (:rewrite nth-of-nats=>chars)
      (:definition natp)
      (:rewrite nth-of-effective-fat)
      (:linear nth-when-d-e-p)
      (:rewrite explode-of-d-e-filename)
      (:rewrite
       hifat-entry-count-of-lofat-to-hifat-helper-of-delete-d-e-lemma-3)
      (:rewrite d-e-p-when-member-equal-of-d-e-list-p)
      (:rewrite take-of-len-free)
      (:rewrite natp-of-car-when-nat-listp))))))

(defthm
  lofat-place-file-correctness-lemma-46
  (implies
   (and
    (not
     (member-intersectp-equal
      x
      (mv-nth
       2
       (lofat-to-hifat-helper fat32$c
                              d-e-list entry-limit1))))
    (equal
     (mv-nth 3
             (lofat-to-hifat-helper fat32$c
                                    d-e-list entry-limit1))
     0)
    (>=
     (nfix entry-limit2)
     (mv-nth
      1
      (lofat-to-hifat-helper fat32$c
                             d-e-list entry-limit1))))
   (not
    (member-intersectp-equal
     x
     (mv-nth
      2
      (lofat-to-hifat-helper fat32$c
                             d-e-list entry-limit2)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable lofat-to-hifat-helper-correctness-4)
    :use lofat-to-hifat-helper-correctness-4)))

(defthm
  lofat-place-file-correctness-lemma-83
  (implies
   (and
    (equal (mv-nth 3
                   (lofat-to-hifat-helper fat32$c
                                          d-e-list entry-limit1))
           0)
    (<=
     x
     (binary-+
      y
      (binary-+
       z
       (unary--
        (hifat-entry-count
         (mv-nth 0
                 (lofat-to-hifat-helper fat32$c
                                        d-e-list entry-limit1)))))))
    (>= (nfix entry-limit2)
        (mv-nth 1
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit1))))
   (<=
    x
    (binary-+
     y
     (binary-+
      z
      (unary--
       (hifat-entry-count
        (mv-nth 0
                (lofat-to-hifat-helper fat32$c
                                       d-e-list entry-limit2))))))))
  :hints (("goal" :in-theory (disable lofat-to-hifat-helper-correctness-4)
           :use lofat-to-hifat-helper-correctness-4)))

(defthm
  lofat-remove-file-correctness-lemma-26
  (implies
   (and
    (good-root-d-e-p root-d-e fat32$c)
    (equal
     (mv-nth
      3
      (lofat-to-hifat-helper
       fat32$c
       (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
       entry-limit))
     0)
    (d-e-directory-p
     (mv-nth
      0
      (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
                name))))
   (good-root-d-e-p
    (mv-nth
     0
     (find-d-e (make-d-e-list (mv-nth 0 (d-e-cc-contents fat32$c root-d-e)))
               name))
    fat32$c))
  :hints
  (("goal" :do-not-induct t
    :in-theory (enable hifat-remove-file
                       (:rewrite lofat-to-hifat-inversion-lemma-4)
                       lofat-to-hifat-inversion-lemma-15
                       good-root-d-e-p))))

;; slightly better version of d-e-cc-contents-of-clear-cc.
(defthm
  lofat-place-file-guard-lemma-9
  (implies
   (and (lofat-fs-p fat32$c)
        (d-e-directory-p d-e1)
        (not (intersectp-equal (mv-nth '0 (d-e-cc fat32$c d-e1))
                               (mv-nth '0 (d-e-cc fat32$c d-e2)))))
   (equal (d-e-cc-contents (mv-nth 0
                                   (clear-cc fat32$c (d-e-first-cluster d-e1)
                                             *ms-max-dir-size*))
                           d-e2)
          (d-e-cc-contents fat32$c d-e2)))
  :hints
  (("goal" :in-theory (e/d (d-e-cc)
                           (d-e-cc-contents-of-clear-cc))
    :use (:instance d-e-cc-contents-of-clear-cc (d-e d-e2)
                    (masked-current-cluster (d-e-first-cluster d-e1))
                    (length *ms-max-dir-size*)))))

;; slightly better version of d-e-cc-contents-of-clear-cc.
(defthm
  lofat-place-file-guard-lemma-11
  (implies
   (and (lofat-fs-p fat32$c)
        (not (d-e-directory-p d-e1))
        (not (intersectp-equal (mv-nth '0 (d-e-cc fat32$c d-e1))
                               (mv-nth '0 (d-e-cc fat32$c d-e2)))))
   (equal (d-e-cc-contents (mv-nth 0
                                   (clear-cc fat32$c (d-e-first-cluster d-e1)
                                             (d-e-file-size d-e1)))
                           d-e2)
          (d-e-cc-contents fat32$c d-e2)))
  :hints
  (("goal" :in-theory (e/d (d-e-cc)
                           (d-e-cc-contents-of-clear-cc))
    :use (:instance d-e-cc-contents-of-clear-cc (d-e d-e2)
                    (masked-current-cluster (d-e-first-cluster d-e1))
                    (length (d-e-file-size d-e1))))))
