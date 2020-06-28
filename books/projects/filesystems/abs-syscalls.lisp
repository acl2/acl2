;  abs-syscalls.lisp                                    Mihir Mehta

; This is a model of the FAT32 filesystem, related to HiFAT but with abstract
; variables.

(in-package "ACL2")

(include-book "abs-find-file")
(include-book "hifat-syscalls")
(local (include-book "std/lists/prefixp" :dir :system))
(local (include-book "std/lists/intersectp" :dir :system))

(local (in-theory (e/d (abs-file-p-when-m1-regular-file-p
                        nat-listp-of-strip-cars-when-frame-p
                        len-when-consp)
                       ((:definition member-equal)
                        (:rewrite
                         abs-addrs-when-m1-file-alist-p-lemma-2)
                        (:rewrite m1-directory-file-p-correctness-1)
                        (:rewrite assoc-of-car-when-member)
                        (:rewrite integerp-of-car-when-integer-listp)
                        (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                        (:linear
                         len-when-hifat-bounded-file-alist-p . 1)
                        (:rewrite
                         m1-file-p-of-cdar-when-m1-file-alist-p)
                        (:definition integer-listp)
                        (:rewrite natp-of-car-when-nat-listp)))))

;; Let's try to do this intuitively first...

(defund abs-place-file-helper (fs path file)
  (declare (xargs :guard (and (abs-fs-p fs) (abs-file-p file) (fat32-filename-list-p path))
                  :measure (len path)))
  (b* ((fs (mbe :exec fs :logic (abs-fs-fix fs)))
       ((unless (consp path)) (mv fs *enoent*))
       (name (fat32-filename-fix (car path)))
       (alist-elem (abs-assoc name fs))
       ((unless (consp alist-elem)) (if (consp (cdr path)) (mv fs *enotdir*)
                                      (mv (abs-put-assoc name file fs) 0)))
       ((when (and (not (abs-directory-file-p (cdr alist-elem)))
                   (or (consp (cdr path)) (abs-directory-file-p file))))
        (mv fs *enotdir*))
       ((when (not (or (abs-directory-file-p (cdr alist-elem))
                       (consp (cdr path)) (abs-directory-file-p file)
                       (and (atom alist-elem) (>= (len fs) *ms-max-dir-ent-count*)))))
        (mv (abs-put-assoc name file fs) 0))
       ((when (not (or (m1-regular-file-p (cdr alist-elem))
                       (consp (cdr path)) (m1-regular-file-p file)
                       (and (atom alist-elem) (>= (len fs) *ms-max-dir-ent-count*)))))
        (mv (abs-put-assoc name file fs) 0))
       ((when (and (atom alist-elem) (>= (len fs) *ms-max-dir-ent-count*))) (mv fs *enospc*))
       ((mv new-contents error-code) (abs-place-file-helper (abs-file->contents (cdr alist-elem))
                                                            (cdr path) file)))
    (mv (abs-put-assoc name (make-abs-file :dir-ent (abs-file->dir-ent (cdr alist-elem))
                                           :contents new-contents)
                       fs)
        error-code)))

(defthm
  abs-file-alist-p-of-abs-place-file-helper
  (implies
   (abs-file-p file)
   (abs-file-alist-p (mv-nth 0
                             (abs-place-file-helper fs path file))))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(defthm
  abs-no-dups-p-of-abs-place-file-helper
  (implies (and (abs-file-p file)
                (or (m1-regular-file-p file)
                    (abs-no-dups-p (abs-file->contents file))))
           (abs-no-dups-p (mv-nth 0
                                  (abs-place-file-helper fs path file))))
  :hints (("goal" :in-theory (enable abs-place-file-helper abs-no-dups-p)
           :induct (abs-place-file-helper fs path file))))

(defthm
  abs-fs-p-of-abs-place-file-helper-lemma-1
  (implies (m1-regular-file-p file)
           (abs-no-dups-p (abs-file->contents file)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-file->contents m1-regular-file-p
                              m1-file-contents-fix abs-no-dups-p)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (m1-regular-file-p file)
             (abs-no-dups-p (m1-file->contents file))))))

(defthm
  abs-fs-p-of-abs-place-file-helper
  (implies (and (abs-file-p file)
                (abs-no-dups-p (abs-file->contents file)))
           (abs-fs-p (mv-nth 0
                             (abs-place-file-helper fs path file))))
  :hints (("goal" :in-theory (enable abs-fs-p))))

(defund
  abs-place-file (frame path file)
  (declare
   (xargs :guard (and (frame-p frame)
                      (abs-file-p file)
                      (fat32-filename-list-p path))
          :guard-hints (("Goal" :do-not-induct t) )))
  (b*
      (((when (atom frame))
        (mv frame *enoent*))
       (path (mbe :exec path
                      :logic (fat32-filename-list-fix path)))
       ((mv tail tail-error-code)
        (abs-place-file (cdr frame) path file))
       ((unless (and (equal tail-error-code *ENOENT*)
                     (prefixp (frame-val->path (cdar frame))
                              path)))
        (mv (list* (car frame) tail) tail-error-code))
       ;; Look up the parent directory - it has to be in one of the variables,
       ;; or else we must return ENOENT.
       ((mv & error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 (butlast path 1))))
       ((when (or (equal error-code *enoent*)
                  (not (abs-complete (frame-val->dir (cdar frame))))))
        (mv (list* (car frame) tail) tail-error-code))
       ((mv head head-error-code)
        (abs-place-file-helper (frame-val->dir (cdar frame)) path file)))
    (mv
     (list* (cons (caar frame) (change-frame-val (cdar frame)
                                                 :dir (abs-fs-fix head)))
            (cdr frame))
     head-error-code)))

(defund
  path-clear (path frame)
  (declare (xargs :guard (and (fat32-filename-list-p path)
                              (frame-p frame))
                  :guard-debug t))
  (b*
      (((when (atom frame)) t)
       ((unless
            (path-clear path (cdr frame)))
        nil)
       (path (mbe :exec path :logic (fat32-filename-list-fix
                                             path))))
    (and
     (or
      (not (prefixp
            path
            (frame-val->path (cdar frame))))
      (equal
       (frame-val->path (cdar frame))
       path))
     (or
      (not (prefixp
            (frame-val->path (cdar frame))
            path))
      (atom
       (names-at (frame-val->dir (cdar frame))
                 (nthcdr
                  (len (frame-val->path (cdar frame)))
                  path)))))))

(defthm
  path-clear-of-frame-with-root
  (iff (path-clear path (frame-with-root root frame))
       (and (path-clear path frame)
            (not (consp (names-at root path)))))
  :hints (("goal" :in-theory (enable path-clear frame-with-root names-at)
           :do-not-induct t))
  :otf-flg t)

(defthm
  dist-names-when-path-clear
  (implies (path-clear path frame)
           (dist-names dir path frame))
  :hints (("goal" :in-theory (enable dist-names
                                     path-clear prefixp intersectp-equal)
           :induct (path-clear path frame)
           :expand (dist-names dir path frame))))

(defthm
  hifat-subsetp-of-put-assoc-1
  (implies
   (and (m1-file-alist-p x)
        (hifat-no-dups-p x)
        (stringp name))
   (equal
    (hifat-subsetp (put-assoc-equal name val x)
                   y)
    (and
     (hifat-subsetp (remove-assoc-equal name x)
                    y)
     (consp (assoc-equal name y))
     (or
      (and (not (m1-directory-file-p (cdr (assoc-equal name y))))
           (not (m1-directory-file-p val))
           (equal (m1-file->contents val)
                  (m1-file->contents (cdr (assoc-equal name y)))))
      (and (m1-directory-file-p (cdr (assoc-equal name y)))
           (m1-directory-file-p val)
           (hifat-subsetp (m1-file->contents val)
                          (m1-file->contents (cdr (assoc-equal name y)))))))))
  :hints (("goal" :in-theory (enable hifat-subsetp)
           :induct (mv (put-assoc-equal name val x)
                       (remove-assoc-equal name x)))))

(defthm hifat-subsetp-of-put-assoc-2
  (implies (and (m1-file-alist-p x)
                (hifat-subsetp x (remove-assoc-equal name y)))
           (hifat-subsetp x (put-assoc-equal name val y)))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm hifat-subsetp-of-remove-assoc-1
  (implies (and (m1-file-alist-p x)
                (atom (assoc-equal name x))
                (hifat-subsetp x y))
           (hifat-subsetp x (remove-assoc-equal name y)))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm hifat-subsetp-of-remove-assoc-2
  (implies (hifat-subsetp x y)
           (hifat-subsetp (remove-assoc-equal name x)
                          y))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm
  hifat-place-file-correctness-lemma-3
  (implies
   (and
    (not
     (m1-regular-file-p (cdr (assoc-equal (fat32-filename-fix (car path))
                                          x))))
    (m1-file-alist-p x)
    (hifat-subsetp y x))
   (not
    (m1-regular-file-p (cdr (assoc-equal (fat32-filename-fix (car path))
                                         y)))))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthmd
  hifat-place-file-correctness-lemma-1
  (implies (and (m1-file-alist-p x)
                (m1-file-alist-p y)
                (hifat-no-dups-p x)
                (hifat-no-dups-p y)
                (hifat-subsetp x y)
                (hifat-subsetp y x)
                (hifat-no-dups-p (m1-file->contents file)))
           (and (hifat-subsetp (mv-nth 0 (hifat-place-file y path file))
                               (mv-nth 0 (hifat-place-file x path file)))
                (equal (mv-nth 1 (hifat-place-file y path file))
                       (mv-nth 1 (hifat-place-file x path file)))))
  :hints (("goal" :in-theory (enable hifat-place-file hifat-subsetp))))

;; This isn't a congruence rule, so it may have to be left disabled...
(defthmd
  hifat-place-file-correctness-4
  (implies
   (and (hifat-equiv m1-file-alist2 m1-file-alist1)
        (hifat-no-dups-p (m1-file->contents file)))
   (and
    (equal (mv-nth 1
                   (hifat-place-file m1-file-alist2 path file))
           (mv-nth 1
                   (hifat-place-file m1-file-alist1 path file)))
    (hifat-equiv (mv-nth 0
                         (hifat-place-file m1-file-alist2 path file))
                 (mv-nth 0
                         (hifat-place-file m1-file-alist1 path file)))))
  :hints
  (("goal" :in-theory (enable hifat-place-file hifat-equiv)
    :use ((:instance (:rewrite hifat-place-file-correctness-lemma-1)
                     (x (hifat-file-alist-fix m1-file-alist2))
                     (file file)
                     (path path)
                     (y (hifat-file-alist-fix m1-file-alist1)))
          (:instance (:rewrite hifat-place-file-correctness-lemma-1)
                     (x (hifat-file-alist-fix m1-file-alist1))
                     (file file)
                     (path path)
                     (y (hifat-file-alist-fix m1-file-alist2))))
    :do-not-induct t)))

;; Probably tricky to get a refinement relationship (in the defrefinement
;; sense) between literally absfat-equiv and hifat-equiv. But we can still have
;; some kind of substitute...
(encapsulate
  ()

  (local
   (defthmd lemma
     (implies (and (m1-file-alist-p abs-file-alist1)
                   (m1-file-alist-p abs-file-alist2)
                   (hifat-no-dups-p abs-file-alist1)
                   (hifat-no-dups-p abs-file-alist2))
              (equal (absfat-equiv abs-file-alist1 abs-file-alist2)
                     (hifat-equiv abs-file-alist1 abs-file-alist2)))
     :hints (("goal" :in-theory (enable absfat-equiv hifat-equiv abs-fs-p
                                        absfat-subsetp-correctness-1)))))

  (defthm
    hifat-equiv-when-absfat-equiv
    (implies (and (m1-file-alist-p (abs-fs-fix abs-file-alist1))
                  (m1-file-alist-p (abs-fs-fix abs-file-alist2)))
             (equal (absfat-equiv abs-file-alist1 abs-file-alist2)
                    (hifat-equiv (abs-fs-fix abs-file-alist1)
                                 (abs-fs-fix abs-file-alist2))))
    :hints
    (("goal" :use (:instance lemma
                             (abs-file-alist1 (abs-fs-fix abs-file-alist1))
                             (abs-file-alist2 (abs-fs-fix abs-file-alist2)))))))

(defthm abs-fs-p-when-hifat-no-dups-p
  (implies (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs))
           (abs-fs-p fs))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-fs-p))))

(defthm
  absfat-place-file-correctness-lemma-3
  (implies
   (and
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (abs-fs-p dir)
    (not (consp (abs-addrs dir)))
    (path-clear nil frame)
    (not (consp (names-at root nil)))
    (abs-fs-p root)
    (not (zp x))
    (not (consp (assoc-equal 0 frame)))
    (frame-p frame)
    (not (consp (assoc-equal x frame)))
    (no-duplicatesp-equal (strip-cars frame))
    (subsetp-equal
     (abs-addrs root)
     (frame-addrs-root
      (cons (cons x
                  (frame-val nil
                             (put-assoc-equal (car (last path))
                                              file dir)
                             src))
            frame)))
    (mv-nth 1
            (collapse (frame-with-root root
                                       (cons (cons x (frame-val nil dir src))
                                             frame))))
    (absfat-equiv
     (mv-nth 0
             (collapse (frame-with-root root
                                        (cons (cons x (frame-val nil dir src))
                                              frame))))
     fs)
    (no-duplicatesp-equal (abs-addrs root))
    (not (intersectp-equal nil (names-at dir nil)))
    (abs-separate frame))
   (hifat-equiv
    fs
    (mv-nth 0
            (collapse (frame-with-root root
                                       (cons (cons x (frame-val nil dir src))
                                             frame))))))
  :hints (("goal" :in-theory (enable abs-separate
                                     dist-names hifat-equiv-when-absfat-equiv
                                     frame-addrs-root))))

(defthm
  absfat-place-file-correctness-lemma-4
  (implies
   (subsetp-equal
    (abs-addrs root)
    (frame-addrs-root
     (cons (cons x
                 (frame-val nil
                            (put-assoc-equal (car (last path))
                                             file dir)
                            src))
           frame)))
   (subsetp-equal (abs-addrs root)
                  (frame-addrs-root (cons (cons x (frame-val 'nil dir src))
                                          frame))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (hifat-equiv-when-absfat-equiv dist-names
                                        abs-separate frame-addrs-root)
         nil)))
  :otf-flg t)

(defthm
  absfat-place-file-correctness-lemma-5
  (implies
   (and
    (hifat-equiv
     (mv-nth
      0
      (collapse
       (frame-with-root
        root
        (cons (cons x
                    (frame-val nil
                               (put-assoc-equal (car (last path))
                                                file dir)
                               src))
              frame))))
     (mv-nth
      0
      (hifat-place-file
       fs nil
       (m1-file
        (m1-file->dir-ent
         (mv-nth
          0
          (hifat-find-file
           (mv-nth
            0
            (collapse (frame-with-root root
                                       (cons (cons x (frame-val nil dir src))
                                             frame))))
           nil)))
        (put-assoc-equal (car (last path))
                         file dir)))))
    (equal (mv-nth 1
                   (hifat-place-file fs nil
                                     (put-assoc-equal (car (last path))
                                                      file dir)))
           0))
   (hifat-equiv
    (mv-nth
     0
     (collapse
      (frame-with-root
       root
       (cons (cons x
                   (frame-val nil
                              (put-assoc-equal (car (last path))
                                               file dir)
                              src))
             frame))))
    (mv-nth 0 (hifat-place-file fs path file))))
  :instructions
  (:promote
   (:=
    (mv-nth
     0
     (collapse
      (frame-with-root
       root
       (cons (cons x
                   (frame-val nil
                              (put-assoc-equal (car (last path))
                                               file dir)
                              src))
             frame))))
    (mv-nth
     0
     (hifat-place-file
      fs nil
      (m1-file
       (m1-file->dir-ent
        (mv-nth
         0
         (hifat-find-file
          (mv-nth
           0
           (collapse (frame-with-root root
                                      (cons (cons x (frame-val nil dir src))
                                            frame))))
          nil)))
       (put-assoc-equal (car (last path))
                        file dir))))
    :equiv hifat-equiv)
   (:bash ("goal" :in-theory (enable hifat-place-file)))))

(defthm absfat-place-file-correctness-lemma-6
  (implies (and (abs-fs-p dir)
                (not (member-equal (car (last path))
                                   (names-at dir nil))))
           (not (consp (assoc-equal (car (last path))
                                    dir))))
  :hints (("goal" :in-theory (enable names-at))))

(defthm abs-file-p-when-m1-file-p
  (implies (m1-file-p file)
           (abs-file-p file))
  :hints (("goal" :cases ((abs-directory-file-p file)))))

(defthm
  m1-file-p-of-abs-file
  (equal (m1-file-p (abs-file dir-ent contents))
         (or (stringp (abs-file-contents-fix contents))
             (m1-file-alist-p contents)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-file-p abs-file abs-file-contents-fix
                              abs-file-contents-p
                              m1-file-contents-p))))

(defthm
  m1-file-alist-p-of-abs-place-file-helper
  (implies
   (and (abs-complete (abs-fs-fix fs))
        (m1-file-p file))
   (m1-file-alist-p (mv-nth 0
                            (abs-place-file-helper fs path file))))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(defthm abs-place-file-helper-of-abs-fs-fix
  (equal (abs-place-file-helper (abs-fs-fix fs) path file)
         (abs-place-file-helper fs path file))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(encapsulate
  ()

  (local
   (defthm
     lemma
     (implies (and (m1-file-alist-p fs)
                   (hifat-no-dups-p fs)
                   ;; This hypothesis is suboptimal... I know.
                   (m1-file-p file))
              (equal (abs-place-file-helper fs path file)
                     (hifat-place-file fs path file)))
     :hints
     (("goal"
       :in-theory (enable abs-place-file-helper hifat-place-file
                          abs-file m1-file abs-file->dir-ent
                          m1-file->dir-ent abs-fs-p)
       :induct (abs-place-file-helper fs path file)))))

  (defthm
    abs-place-file-helper-correctness-1
    (implies (and (abs-complete (abs-fs-fix fs))
                  (m1-file-p file))
             (equal (abs-place-file-helper fs path file)
                    (hifat-place-file (abs-fs-fix fs)
                                      path file)))
    :hints (("goal" :in-theory (disable lemma)
             :use (:instance lemma
                             (fs (abs-fs-fix fs)))))))

(defthm
  abs-top-addrs-of-abs-place-file-helper
  (equal (abs-top-addrs (mv-nth 0
                                (abs-place-file-helper fs path file)))
         (abs-top-addrs fs))
  :hints (("goal" :in-theory (enable abs-top-addrs abs-place-file-helper))))

(defthm
  addrs-at-when-abs-complete
  (implies (abs-complete (abs-fs-fix fs))
           (equal (addrs-at fs relpath) nil))
  :hints
  (("goal" :in-theory (enable addrs-at)
    :induct (addrs-at fs relpath))
   ("subgoal *1/1''" :in-theory (disable ctx-app-ok-when-abs-complete-lemma-3)
    :use ctx-app-ok-when-abs-complete-lemma-3)))

(defthm
  addrs-at-of-abs-place-file-helper-lemma-1
  (implies (and (m1-file-p file)
                (or (m1-regular-file-p file)
                    (hifat-no-dups-p (m1-file->contents file))))
           (not (addrs-at (m1-file->contents file)
                          (cdr relpath))))
  :hints
  (("goal" :in-theory
    (e/d (m1-file-contents-p addrs-at m1-regular-file-p
                             m1-file-p m1-file->contents abs-fs-fix)
         (m1-file-contents-p-of-m1-file->contents))
    :use (:instance m1-file-contents-p-of-m1-file->contents
                    (x file))
    :do-not-induct t))
  :otf-flg t)

(defthm
  addrs-at-of-abs-place-file-helper-1
  (implies (and (abs-file-p file)
                (abs-no-dups-p (abs-file->contents file)))
           (equal (addrs-at (mv-nth 0
                                    (abs-place-file-helper fs path file))
                            relpath)
                  (if (and
                       (zp (mv-nth 1
                                   (abs-place-file-helper fs path file)))
                       (prefixp (fat32-filename-list-fix path)
                                (fat32-filename-list-fix relpath)))
                      (addrs-at (abs-file->contents file)
                                (nthcdr (len path) relpath))
                    (addrs-at fs relpath))))
  :hints
  (("goal"
    :in-theory (enable abs-place-file-helper addrs-at)
    :induct (mv (fat32-filename-list-prefixp relpath path)
                (addrs-at fs relpath))
    :expand
    ((abs-place-file-helper fs path file)
     (addrs-at
      (put-assoc-equal
       (fat32-filename-fix (car path))
       (abs-file
        (abs-file->dir-ent
         (cdr (assoc-equal (fat32-filename-fix (car path))
                           fs)))
        (mv-nth
         0
         (abs-place-file-helper
          (abs-file->contents
           (cdr (assoc-equal (fat32-filename-fix (car path))
                             fs)))
          (cdr path)
          file)))
       fs)
      relpath)))))

(defthm natp-of-abs-place-file-helper
  (natp (mv-nth 1
                (abs-place-file-helper fs path file)))
  :hints (("goal" :in-theory (enable abs-place-file-helper)))
  :rule-classes :type-prescription)

(defthm abs-place-file-helper-correctness-2
  (implies (not (zp (mv-nth 1
                            (abs-place-file-helper fs path file))))
           (equal (mv-nth 0
                          (abs-place-file-helper fs path file))
                  (abs-fs-fix fs)))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(defthm ctx-app-ok-of-abs-place-file-helper-lemma-1
  (implies (stringp x)
           (equal (addrs-at x relpath) nil))
  :hints (("goal" :in-theory (enable addrs-at abs-fs-fix)))
  :rule-classes (:type-prescription :rewrite))

(defthm
  ctx-app-ok-of-abs-place-file-helper-1
  (implies
   (and (abs-file-p file)
        (abs-no-dups-p (abs-file->contents file)))
   (equal (ctx-app-ok (mv-nth 0
                              (abs-place-file-helper fs path file))
                      x x-path)
          (if (and (zp (mv-nth 1
                               (abs-place-file-helper fs path file)))
                   (prefixp (fat32-filename-list-fix path)
                            (fat32-filename-list-fix x-path)))
              (ctx-app-ok (abs-file->contents file)
                          x (nthcdr (len path) x-path))
              (ctx-app-ok fs x x-path))))
  :hints (("goal" :in-theory (enable ctx-app-ok)
           :do-not-induct t))
  :otf-flg t)

(defthm natp-of-abs-place-file-helper
  (natp (mv-nth 1
                (abs-place-file-helper fs path file)))
  :hints (("goal" :in-theory (enable abs-place-file-helper)))
  :rule-classes :type-prescription)

(defthm names-at-of-abs-place-file-helper-lemma-1
  (implies (and (abs-file-p file)
                (not (abs-directory-file-p file)))
           (not (names-at (abs-file->contents file)
                          (nthcdr 1 relpath))))
  :hints (("goal" :in-theory (enable names-at abs-directory-file-p
                                     abs-file-p abs-file->contents
                                     abs-file-contents-p abs-fs-fix)
           :do-not-induct t)))

(defthm
  names-at-of-abs-place-file-helper-lemma-2
  (implies (m1-regular-file-p file)
           (not (names-at (m1-file->contents file)
                          (nthcdr 1 relpath))))
  :hints (("goal" :in-theory (enable names-at
                                     abs-directory-file-p m1-regular-file-p
                                     abs-file-p abs-file->contents
                                     abs-file-contents-p abs-fs-fix)
           :do-not-induct t)))

(defthm names-at-of-abs-place-file-helper-lemma-3
  (implies (and (abs-no-dups-p (abs-file->contents file))
                (abs-directory-file-p file))
           (abs-fs-p (abs-file->contents file)))
  :hints (("goal" :in-theory (enable abs-directory-file-p)
           :do-not-induct t)))

(defthm names-at-of-abs-place-file-helper-lemma-5
  (implies (m1-regular-file-p file)
           (equal (strip-cars (abs-fs-fix (m1-file->contents file)))
                  nil))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-regular-file-p
                              abs-file-p abs-file->contents
                              abs-fs-fix abs-file-contents-p))))

;; (b* ((fs (list (cons (coerce (name-to-fat32-name (coerce "var" 'list)) 'string)
;;                      (make-abs-file))
;;                (cons (coerce (name-to-fat32-name (coerce
;;                                                   "tmp"
;;                                                   'list))
;;                              'string)
;;                      (make-abs-file
;;                       :contents (list
;;                                  (cons
;;                                   (coerce
;;                                    (name-to-fat32-name
;;                                     (coerce
;;                                      "pipe"
;;                                      'list))
;;                                    'string)
;;                                   (make-abs-file)))))))
;;      ((mv val &) (abs-place-file-helper fs (path-to-fat32-path
;;                                             (coerce "/tmp/hspid" 'list))
;;                                         (make-abs-file))))
;;   (list (names-at val
;;                   (path-to-fat32-path
;;                    (coerce
;;                     "/tmp"
;;                     'list)))
;;         (names-at fs
;;                   (path-to-fat32-path
;;                    (coerce
;;                     "/tmp"
;;                     'list)))))

(defthm
  names-at-of-abs-place-file-helper-1
  (implies
   (abs-file-p file)
   (equal
    (names-at (mv-nth 0
                      (abs-place-file-helper fs path file))
              relpath)
    (cond ((not (zp (mv-nth 1
                            (abs-place-file-helper fs path file))))
           (names-at fs relpath))
          ((fat32-filename-list-prefixp path relpath)
           (names-at (abs-file->contents file)
                     (nthcdr (len path) relpath)))
          ((and (fat32-filename-list-equiv relpath (butlast path 1))
                (not (member-equal (fat32-filename-fix (car (last path)))
                                   (names-at fs relpath))))
           (append (names-at fs relpath)
                   (list (fat32-filename-fix (car (last path))))))
          (t (names-at fs relpath)))))
  :hints
  (("goal" :in-theory
    (e/d (abs-place-file-helper names-at fat32-filename-list-fix
                                fat32-filename-list-equiv
                                fat32-filename-equiv abs-file-p-alt)
         ((:definition put-assoc-equal)
          (:rewrite ctx-app-ok-when-absfat-equiv-lemma-3)
          (:definition abs-complete)
          (:rewrite hifat-find-file-correctness-1-lemma-1)
          (:type-prescription assoc-equal-when-frame-p)
          (:definition assoc-equal)
          (:definition no-duplicatesp-equal)
          (:rewrite m1-file-alist-p-when-subsetp-equal)
          (:rewrite subsetp-when-prefixp)))
    :induct (mv (fat32-filename-list-prefixp relpath path)
                (names-at fs relpath))
    :expand (abs-place-file-helper fs path file))))

;; This is based on collapse-hifat-place-file-2, which relies on the lemma
;; collapse-hifat-place-file-lemma-6. That lemma would probably have to be tweaked to
;; deal with all the path appending stuff, which I'm skipping over for now.
(skip-proofs
 (defthm
   collapse-hifat-place-file-2
   (implies
    (and
     (m1-file-p file)
     (or (m1-regular-file-p file)
         (hifat-no-dups-p (m1-file->contents file)))
     (dist-names (frame->root (frame-with-root root frame))
                 nil
                 (frame->frame (frame-with-root root frame)))
     (abs-separate (frame->frame (frame-with-root root frame)))
     (frame-p (frame->frame (frame-with-root root frame)))
     (no-duplicatesp-equal
      (strip-cars (frame->frame (frame-with-root root frame))))
     (consp (assoc-equal x frame)))
    (and
     (equal
      (mv-nth
       0
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val
           (frame-val->path (cdr (assoc-equal x frame)))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir (cdr (assoc-equal x frame)))
             path file))
           (frame-val->src (cdr (assoc-equal x frame))))
          frame))))
      (mv-nth
       0
       (abs-place-file-helper
        (mv-nth 0
                (collapse (frame-with-root root frame)))
        (append (frame-val->path (cdr (assoc-equal x frame)))
                path)
        file)))
     (equal
      (mv-nth
       1
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val
           (frame-val->path (cdr (assoc-equal x frame)))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir (cdr (assoc-equal x frame)))
             path file))
           (frame-val->src (cdr (assoc-equal x frame))))
          frame))))
      (mv-nth 1
              (collapse (frame-with-root root frame))))))))

;; I guess I should say that this function can only really do so much, and if
;; we try to use this in our proofs we'll kinda be back to representing
;; filesystem trees as... filesystem trees. When I say it can only do so much,
;; I mean that it can only help us do some refinement proofs, which will tie
;; lofat to hifat and hifat to absfat. Ultimately, I guess we'll want theorems
;; that use the collapse-equiv relation defined previously...
(defun frame-reps-fs
    (frame fs)
  (b*
      (((mv fs-equiv result) (collapse frame)))
    (and result
         (absfat-equiv fs-equiv fs)
         (abs-separate frame)
         (subsetp-equal
          (abs-addrs (frame->root frame))
          (frame-addrs-root (frame->frame frame))))))

(defcong absfat-equiv equal (frame-reps-fs frame fs) 2)

;; I'm not even sure what the definition of abs-place-file above should be. But
;; I'm pretty sure it should support a theorem like the following.
;;
;; In the hypotheses here, there has to be a stipulation that not only is dir
;; complete, but also that it's the only one which has any names at that
;; particular relpath, i.e. (butlast path 1). It's codified under
;; path-clear.
;;
;; Also, the use hints in this theorem are awkward but necessary - restrict
;; hints do not work because there's never a real chance for them to be
;; applied, or so :brr tells us.
;;
;; OK, so how do we develop a specification for abs-mkdir which we can actually
;; USE? Like, we would want to say that (abs-mkdir frame) is going to return a
;; new frame and an error code, and that error code will tell us whether to
;; expect an unchanged frame (modulo absfat-equiv) or a new frame with an
;; element right at the front representing the parent directory of the new
;; directory with the new directory inside it.
(defthm
  absfat-place-file-correctness-lemma-2
  (implies
   (and
    (m1-file-alist-p fs)
    (hifat-no-dups-p fs)
    (fat32-filename-list-p path)
    (m1-regular-file-p file)
    (abs-fs-p dir)
    (abs-complete dir)
    (path-clear (butlast path 1)
                    frame)
    (atom (names-at root (butlast path 1)))
    (abs-fs-p root)
    (not (zp x))
    (atom (assoc-equal 0 frame))
    (frame-p frame)
    (not (consp (assoc-equal x frame)))
    (no-duplicatesp-equal (strip-cars frame))
    (frame-reps-fs
     (frame-with-root root
                      (cons (cons x
                                  (frame-val (butlast path 1)
                                             dir src))
                            frame))
     fs)
    (not (member-equal (car (last path))
                       (names-at dir nil)))
    (consp path))
   (b* ((dir (put-assoc-equal (car (last path))
                              file dir))
        (frame (frame-with-root root
                                (cons (cons x
                                            (frame-val (butlast path 1)
                                                       dir src))
                                      frame)))
        ((mv fs &)
         (hifat-place-file fs path file)))
     (frame-reps-fs frame fs)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (hifat-place-file dist-names
                           abs-separate frame-addrs-root)
         (collapse-hifat-place-file-2
          (:rewrite m1-file-alist-p-when-subsetp-equal)
          (:rewrite len-of-remove-assoc-when-no-duplicatesp-strip-cars)
          (:linear len-of-remove-assoc-1)
          (:definition remove-assoc-equal)
          (:rewrite subsetp-trans)
          (:rewrite abs-addrs-of-put-assoc-lemma-2)
          (:rewrite collapse-congruence-lemma-4)
          member-of-abs-addrs-when-natp
          (:linear position-equal-ac-when-member)
          (:rewrite 1st-complete-of-put-assoc-lemma-1)
          (:definition hifat-file-alist-fix)
          (:rewrite hifat-find-file-correctness-1-lemma-1)
          (:type-prescription ctx-app-list-when-set-equiv-lemma-4)
          (:rewrite m1-directory-file-p-when-m1-file-p)
          (:rewrite abs-no-dups-p-of-put-assoc-equal)
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite
           ctx-app-ok-when-absfat-equiv-lemma-3)
          (:type-prescription assoc-when-zp-len)
          (:definition take)
          (:rewrite take-of-len-free)
          (:rewrite take-of-too-many)
          (:definition true-listp)
          (:rewrite true-listp-when-string-list)
          (:definition string-listp)))
    :use
    ((:instance collapse-hifat-place-file-2
                (frame (cons (cons x
                                   (frame-val (butlast path 1)
                                              dir src))
                             frame))
                (path (last path)))
     (:instance
      (:rewrite hifat-place-file-correctness-4)
      (file file)
      (path path)
      (m1-file-alist2
       (mv-nth
        0
        (collapse
         (frame-with-root
          root
          (cons (cons x
                      (frame-val (take (+ -1 (len path)) path)
                                 dir src))
                frame)))))
      (m1-file-alist1 fs))))))

(defthm
  frame-p-of-abs-place-file
  (implies (frame-p frame)
           (frame-p (mv-nth 0 (abs-place-file
                               frame
                               path
                               file))))
  :hints (("Goal" :in-theory (enable abs-place-file))))

(defund
  abs-remove-file (frame path)
  (declare
   (xargs :guard (and (frame-p frame)
                      (fat32-filename-list-p path))
          :guard-hints (("Goal" :do-not-induct t) )))
  (b*
      (((when (atom frame))
        (mv frame *enoent*))
       (path (mbe :exec path
                      :logic (fat32-filename-list-fix path)))
       ((mv tail tail-error-code)
        (abs-remove-file (cdr frame) path))
       ((unless (and (equal tail-error-code *ENOENT*)
                     (prefixp (frame-val->path (cdar frame))
                              path)))
        (mv (list* (car frame) tail) tail-error-code))
       ;; Look up the parent directory - it has to be in one of the variables,
       ;; or else we must return ENOENT.
       ((mv & error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 (butlast path 1))))
       ((when (or (equal error-code *enoent*)
                  (not (abs-complete (frame-val->dir (cdar frame))))))
        (mv (list* (car frame) tail) tail-error-code))
       ((mv head head-error-code)
        (hifat-remove-file (frame-val->dir (cdar frame)) path)))
    (mv
     (list* (cons (caar frame) (change-frame-val (cdar frame) :dir head))
            (cdr frame))
     head-error-code)))

(defund abs-disassoc (fs path new-index)
  (declare (xargs :guard
                  (and (fat32-filename-list-p path)
                       (abs-fs-p fs)
                       (natp new-index))
                  :verify-guards nil
                  :measure (len path)))
  (b*
      ((fs (mbe :exec fs :logic (abs-fs-fix fs)))
       (new-index
        (mbe :exec new-index :logic (nfix new-index)))
       ((when (atom path))
        (mv fs (list new-index)))
       (alist-elem (abs-assoc
                    (mbe :exec (car path) :logic (fat32-filename-fix (car path)))
                    fs))
       ((when (or (atom alist-elem)
                  (not (abs-directory-file-p (cdr alist-elem)))))
        (mv nil fs))
       ((mv x y)
        (abs-disassoc
         (abs-file->contents (cdr alist-elem))
         (cdr path)
         new-index)))
    (mv x
        (abs-put-assoc
         (mbe :exec (car path) :logic (fat32-filename-fix (car path)))
         (change-abs-file
          (cdr alist-elem)
          :contents
          y)
         fs))))

(defthm
   abs-fs-p-of-abs-disassoc-1
   (abs-fs-p (mv-nth 1 (abs-disassoc fs path new-index)))
   :hints (("Goal" :in-theory (enable abs-disassoc abs-file-alist-p abs-no-dups-p abs-fs-p)
            :induct (abs-disassoc fs path new-index))))

(defthm abs-fs-p-of-abs-disassoc-2
  (abs-fs-p (mv-nth 0 (abs-disassoc fs path new-index)))
  :hints (("goal" :in-theory (enable abs-disassoc)
           :induct (abs-disassoc fs path new-index))))

(verify-guards abs-disassoc)

(defthmd abs-disassoc-of-fat32-filename-list-fix
  (equal (abs-disassoc fs (fat32-filename-list-fix path)
                       new-index)
         (abs-disassoc fs path new-index))
  :hints (("goal" :in-theory (enable abs-disassoc))))

(defthm abs-disassoc-when-not-natp
  (implies (not (natp new-index))
           (equal (abs-disassoc fs path new-index)
                  (abs-disassoc fs path 0)))
  :hints (("Goal" :in-theory (enable abs-disassoc))))

(defcong
  fat32-filename-list-equiv equal
  (abs-disassoc fs path new-index)
  2
  :hints
  (("goal"
    :use (abs-disassoc-of-fat32-filename-list-fix
          (:instance abs-disassoc-of-fat32-filename-list-fix
                     (path path-equiv))))))

(defcong nat-equiv equal
  (abs-disassoc fs path new-index)
  3
  :hints (("goal" :in-theory (enable abs-disassoc))))

(defthm abs-disassoc-correctness-1
  (implies (and (not (member-equal (nfix new-index)
                                   (abs-addrs (abs-fs-fix fs))))
                (equal (mv-nth 1 (abs-disassoc fs path new-index))
                       (abs-fs-fix fs)))
           (equal (mv-nth 0 (abs-disassoc fs path new-index))
                  nil))
  :hints (("goal" :in-theory (enable abs-disassoc))))

(defthm ctx-app-of-abs-disassoc
  (equal (ctx-app (mv-nth 1 (abs-disassoc fs path new-index))
                  (mv-nth 0 (abs-disassoc fs path new-index))
                  new-index path)
         (abs-fs-fix fs))
  :hints (("goal" :in-theory (enable ctx-app abs-disassoc abs-fs-fix)
           :expand (ctx-app fs nil new-index path))))

(defthm abs-mkdir-guard-lemma-1
  (implies (consp (assoc-equal 0 frame))
           (consp (assoc-equal 0 (partial-collapse frame path))))
  :hints (("goal" :in-theory (enable partial-collapse))))

;; This deliberately follows an almost-identical induction scheme to
;; abs-find-file. It was going to be a part of that function, but that just led
;; to too many failures.
(defund
  abs-find-file-src (frame path)
  (declare
   (xargs :guard (and (frame-p frame)
                      (fat32-filename-list-p path))))
  (b*
      (((when (atom frame)) 0)
       (path (mbe :exec path
                      :logic (fat32-filename-list-fix path)))
       ((unless (prefixp (frame-val->path (cdar frame))
                         path))
        (abs-find-file-src (cdr frame) path))
       ((mv & error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 path)))
       ((when (not (equal error-code *enoent*)))
        (mbe :exec (caar frame) :logic (nfix (caar frame)))))
    (abs-find-file-src (cdr frame) path)))

(defthm
  abs-find-file-src-correctness-2
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (not (equal (mv-nth 1 (abs-find-file frame path))
                    *enoent*)))
   (and
    (consp (assoc-equal (abs-find-file-src frame path)
                        frame))
    (prefixp
     (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                        frame)))
     (fat32-filename-list-fix path))
    (equal
     (abs-find-file-helper
      (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                        frame)))
      (nthcdr (len (frame-val->path
                    (cdr (assoc-equal (abs-find-file-src frame path)
                                      frame))))
              path))
     (abs-find-file frame path))))
  :hints (("goal" :in-theory (enable abs-find-file abs-find-file-src)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (frame-p frame)
          (no-duplicatesp-equal (strip-cars frame))
          (not (equal (mv-nth 1 (abs-find-file frame path))
                      *enoent*)))
     (and
      (prefixp
       (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                          frame)))
       (fat32-filename-list-fix path))
      (equal
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                          frame)))
        (nthcdr
         (len (frame-val->path
               (cdr (assoc-equal (abs-find-file-src frame path)
                                 frame))))
         path))
       (abs-find-file frame path)))))))

(encapsulate ()

  (local
   (defthm
     lemma
     (implies (not (zp (abs-find-file-src frame path)))
              (consp (assoc-equal (abs-find-file-src frame path)
                                  frame)))
     :hints (("goal" :in-theory (enable abs-find-file abs-find-file-src)))))

  (defthm
    abs-find-file-src-correctness-1
    (implies (consp (assoc-equal 0 frame))
             (consp (assoc-equal (abs-find-file-src frame path)
                                 frame)))
    :hints (("goal" :in-theory (enable abs-find-file abs-find-file-src)))
    :rule-classes
    ((:rewrite
      :corollary
      (implies (or (not (zp (abs-find-file-src frame path)))
                   (consp (assoc-equal 0 frame))
                   (and (frame-p frame)
                        (no-duplicatesp-equal (strip-cars frame))
                        (not (equal (mv-nth 1 (abs-find-file frame path))
                                    *enoent*))))
               (consp (assoc-equal (abs-find-file-src frame path)
                                   frame)))
      :hints
      (("goal" :in-theory (disable
                           abs-find-file-src-correctness-2)
        :use
        abs-find-file-src-correctness-2))))))

(defthmd
  abs-find-file-src-of-fat32-filename-list-fix
  (equal
   (abs-find-file-src frame (fat32-filename-list-fix path))
   (abs-find-file-src frame path))
  :hints (("Goal" :in-theory (enable abs-find-file-src))))

(defcong
  fat32-filename-list-equiv
  equal (abs-find-file-src frame path)
  2
  :hints
  (("goal"
    :use
    ((:instance abs-find-file-src-of-fat32-filename-list-fix
                (path path-equiv))
     abs-find-file-src-of-fat32-filename-list-fix))))

(defthm abs-mkdir-guard-lemma-2
  (implies (atom path)
           (equal (1st-complete-under-path frame path)
                  (1st-complete frame)))
  :hints (("goal" :in-theory (enable 1st-complete-under-path
                                     1st-complete prefixp))))

(defthm
  abs-mkdir-guard-lemma-3
  (implies (and (mv-nth 1 (collapse frame))
                (atom path)
                (equal frame
                       (frame-with-root (frame->root frame)
                                        (frame->frame frame))))
           (equal (partial-collapse frame path)
                  (frame-with-root (mv-nth 0 (collapse frame))
                                   nil)))
  :hints (("goal" :in-theory
           (e/d
            (partial-collapse collapse collapse-this)
            ((:definition no-duplicatesp-equal)
             (:rewrite
              partial-collapse-correctness-lemma-24)
             (:definition assoc-equal)
             (:rewrite subsetp-when-prefixp)
             (:definition true-listp)
             (:rewrite put-assoc-equal-without-change . 2)
             abs-separate-of-frame->frame-of-collapse-this-lemma-8
             (:rewrite true-list-fix-when-true-listp)
             (:rewrite true-listp-when-string-list)
             (:definition string-listp)
             (:definition put-assoc-equal)
             (:rewrite remove-assoc-of-put-assoc)
             (:rewrite abs-fs-p-when-hifat-no-dups-p)
             (:definition remove-assoc-equal)
             (:definition remove-equal)
             (:rewrite fat32-filename-p-correctness-1)))
           :induct (collapse frame)
           :expand (partial-collapse frame path))))

(defthm
  abs-mkdir-guard-lemma-4
  (implies
   (and (mv-nth 1
                (collapse (frame-with-root root frame)))
        (atom path)
        (atom (assoc-equal 0 frame))
        (frame-p frame))
   (equal (partial-collapse (frame-with-root root frame)
                            path)
          (frame-with-root (mv-nth 0
                                   (collapse (frame-with-root root frame)))
                           nil)))
  :hints (("goal"
           :in-theory (disable abs-mkdir-guard-lemma-3)
           :use (:instance abs-mkdir-guard-lemma-3
                           (frame (frame-with-root root frame))))))

(defthm abs-mkdir-guard-lemma-5
  (implies (abs-no-dups-p fs)
           (no-duplicatesp-equal (remove-equal nil (strip-cars fs))))
  :hints (("goal" :in-theory (enable abs-no-dups-p))))

(defthm
  abs-mkdir-guard-lemma-6
  (implies
   (no-duplicatesp-equal (strip-cars frame))
   (no-duplicatesp-equal (strip-cars (partial-collapse frame path))))
  :hints (("goal" :in-theory (enable partial-collapse collapse-this))))

(defthm
  abs-mkdir-guard-lemma-7
  (implies
   (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs path)))
   (abs-no-dups-p
    (abs-file->contents (mv-nth 0 (abs-find-file-helper fs path)))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-mkdir-guard-lemma-8
  (implies
   (abs-directory-file-p (mv-nth 0 (abs-find-file frame path)))
   (abs-no-dups-p
    (abs-file->contents (mv-nth 0 (abs-find-file frame path)))))
  :hints (("goal" :in-theory (enable abs-find-file))))

;; OK, here's the plan for defining abs-mkdir. We can proooobably get rid of
;; abs-place-file and abs-remove-file, since those tasks are going to be
;; accomplished by first bringing the parent directory to the front and then
;; doing a put-assoc or a remove-assoc respectively.
(defund abs-mkdir (frame path)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal 0 frame))
                              (fat32-filename-list-p path)
                              (no-duplicatesp-equal (strip-cars frame)))
                  :guard-debug t
                  :guard-hints
                  (("goal"
                    :in-theory (enable abs-find-file-helper abs-fs-p)))))
  (b*
      ((path (mbe :exec path :logic (fat32-filename-list-fix path)))
       (dirname (dirname path)) (frame (partial-collapse frame dirname))
       ;; After partial-collapse, either the parent directory is there in one
       ;; variable, or it isn't there at all.
       ((mv parent-dir error-code) (abs-find-file frame dirname))
       ((unless (or (atom dirname) (and (zp error-code) (abs-directory-file-p parent-dir))))
        (mv frame -1 *enoent*))
       (src (abs-find-file-src frame dirname))
       (new-index (find-new-index
                   ;; Using this, not (strip-cars (frame->frame frame)), to make
                   ;; sure we don't get a zero.
                   (strip-cars frame)))
       ;; It's not even a matter of removing that thing - we need to leave a
       ;; body address in its place...
       ((mv var new-src-dir)
        (abs-disassoc (frame-val->dir (cdr (assoc-equal src frame)))
                      (nthcdr (len (frame-val->path (cdr (assoc-equal src frame)))) dirname)
                      new-index))
       ;; Check somewhere that (basename path) is not already present...
       ((unless (consp path)) (mv frame -1 *enoent*))
       ((when (consp (abs-assoc (basename path) var))) (mv frame -1 *eexist*))
       (frame (put-assoc-equal src (change-frame-val (cdr (assoc-equal src frame))
                                                     :dir new-src-dir)
                               frame))
       (new-var (abs-put-assoc (basename path)
                               (make-abs-file :contents nil
                                              :dir-ent (dir-ent-install-directory-bit
                                                        (dir-ent-fix nil) t))
                               var))
       (frame
        (frame-with-root (frame->root frame)
                         (cons (cons new-index
                                     (frame-val dirname
                                                new-var src))
                               (frame->frame frame)))))
    (mv frame 0 0)))

;; An example demonstrating that both ways of doing mkdir work out the same:
(assert-event
 (equal
  (b*
      ((fs (list (cons (implode (name-to-fat32-name (explode "tmp")))
                       (make-m1-file :contents nil))))
       (frame (frame-with-root fs nil))
       (result1 (frame-reps-fs frame fs))
       ((mv frame & &) (abs-mkdir frame (path-to-fat32-path (explode "/tmp/docs"))))
       ((mv frame error-code result3)
        (abs-mkdir frame
                   (path-to-fat32-path (explode "/tmp/docs/pdf-docs"))))
       ((mv frame result4) (collapse frame)))
    (list (m1-file-alist-p fs) result1 error-code result3 frame
          result4))
  '(T
    T 0 0
    (("TMP        "
      (DIR-ENT 0 0 0 0 0 0 0 0 0 0 0 0
               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (CONTENTS
       ("DOCS       "
        (DIR-ENT 0 0 0 0 0 0 0 0 0 0 0 16
                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
        (CONTENTS
         ("PDF-DOCS   " (DIR-ENT 0 0 0 0 0 0 0 0 0 0 0 16
                                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          (CONTENTS)))))))
    T)))

(assert-event
 (equal
  (b*
      ((fs (list (cons (implode (name-to-fat32-name (explode "tmp")))
                       (make-m1-file :contents nil))))
       ((mv fs & &) (hifat-mkdir fs (path-to-fat32-path (explode "/tmp/docs"))))
       ((mv fs & &)
        (hifat-mkdir fs
                     (path-to-fat32-path (explode "/tmp/docs/pdf-docs")))))
    (list fs))
  '((("TMP        "
      (DIR-ENT 0 0 0 0 0 0 0 0 0 0 0 0
               0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
      (CONTENTS
       ("DOCS       "
        (DIR-ENT 0 0 0 0 0 0 0 0 0 0 0 16
                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
        (CONTENTS
         ("PDF-DOCS   " (DIR-ENT 0 0 0 0 0 0 0 0 0 0 0 16
                                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          (CONTENTS))))))))))

(defthm
  abs-mkdir-correctness-lemma-1
  (implies
   (and
    (equal
     (frame-val->src
      (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                     path)
                        (frame->frame frame))))
     0)
    (< 0
       (1st-complete-under-path (frame->frame frame)
                                    path))
    (no-duplicatesp-equal (abs-addrs (frame->root frame)))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (abs-separate frame))
   (abs-separate
    (collapse-this frame
                   (1st-complete-under-path (frame->frame frame)
                                                path))))
  :hints (("goal" :in-theory (enable collapse-this)
           :do-not-induct t)))

(defthm
  abs-mkdir-correctness-lemma-4
  (implies
   (and
    (< 0
       (1st-complete-under-path (frame->frame frame)
                                    path))
    (not
     (equal
      (frame-val->src
       (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                      path)
                         (frame->frame frame))))
      (1st-complete-under-path (frame->frame frame)
                                   path)))
    (consp
     (assoc-equal
      (frame-val->src
       (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                      path)
                         (frame->frame frame))))
      (frame->frame frame)))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src
         (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                        path)
                           (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->path
      (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                     path)
                        (frame->frame frame)))))
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src
         (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                        path)
                           (frame->frame frame))))
        (frame->frame frame))))
     (1st-complete-under-path (frame->frame frame)
                                  path)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal
          (frame-val->src
           (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                          path)
                             (frame->frame frame))))
          (frame->frame frame)))))
      (frame-val->path
       (cdr (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                      path)
                         (frame->frame frame))))))
    (no-duplicatesp-equal (abs-addrs (frame->root frame)))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (abs-separate frame))
   (abs-separate
    (collapse-this frame
                   (1st-complete-under-path (frame->frame frame)
                                                path))))
  :hints (("goal" :in-theory (enable collapse-this)
           :do-not-induct t)))

(defthm
  abs-mkdir-correctness-lemma-5
  (not
   (consp
    (frame-val->path
     (cdr
      (assoc-equal
       0
       (collapse-this frame
                      (1st-complete-under-path (frame->frame frame)
                                                   path)))))))
  :hints (("goal" :in-theory (enable collapse-this
                                     frame->root frame-with-root)
           :do-not-induct t)))

(defthm
  abs-mkdir-correctness-lemma-6
  (implies (and (no-duplicatesp-equal (abs-addrs (frame->root frame)))
                (atom (frame-val->path (cdr (assoc-equal 0 frame))))
                (frame-p (frame->frame frame))
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (abs-separate frame))
           (abs-separate (partial-collapse frame path)))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthm
  abs-mkdir-correctness-lemma-7
  (implies
   (and (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (abs-separate (frame-with-root (frame->root frame)
                                       (frame->frame frame)))
        (subsetp (abs-addrs (frame->root frame))
                 (frame-addrs-root (frame->frame frame))))
   (subsetp-equal
    (abs-addrs (frame->root (partial-collapse frame path)))
    (frame-addrs-root (frame->frame (partial-collapse frame path)))))
  :hints (("goal" :in-theory (enable partial-collapse)
           :induct (partial-collapse frame path))))

(defthm
  abs-mkdir-correctness-lemma-8
  (not (consp (assoc-equal (find-new-index (strip-cars alist))
                           alist)))
  :hints (("goal" :in-theory (disable member-of-strip-cars)
           :use (:instance member-of-strip-cars
                           (x (find-new-index (strip-cars alist))))))
  :rule-classes (:rewrite :type-prescription))

(defthm
  abs-mkdir-correctness-lemma-9
  (implies
   (consp (assoc-equal 0 alist))
   (not (equal (find-new-index (strip-cars alist)) 0)))
  :hints (("Goal" :in-theory
           (disable
            abs-mkdir-correctness-lemma-8)
           :use
           abs-mkdir-correctness-lemma-8))
  :rule-classes
  (:rewrite
   (:linear
    :corollary
    (implies
     (consp (assoc-equal 0 alist))
     (< 0 (find-new-index (strip-cars alist)))))
   (:type-prescription
    :corollary
    (implies
     (consp (assoc-equal 0 alist))
     (< 0 (find-new-index (strip-cars alist)))))))

(defthm abs-mkdir-correctness-lemma-11
  (equal (frame->root (put-assoc-equal 0 val frame))
         (frame-val->dir val))
  :hints (("goal" :do-not-induct t
           :in-theory (enable frame->root))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (natp new-index)
      (equal (addrs-at (mv-nth 1 (abs-disassoc fs path new-index))
                       relpath)
             (cond ((or (equal (mv-nth 1 (abs-disassoc fs path new-index))
                               (abs-fs-fix fs))
                        (not (fat32-filename-list-prefixp path relpath)))
                    (addrs-at (abs-fs-fix fs) relpath))
                   ((fat32-filename-list-equiv relpath path)
                    (list (nfix new-index)))
                   (t nil))))
     :hints
     (("goal"
       :in-theory (e/d (abs-top-addrs addrs-at
                                      abs-disassoc fat32-filename-list-fix
                                      fat32-filename-list-equiv fat32-filename-equiv
                                      abs-fs-p abs-file-alist-p abs-no-dups-p)
                       ((:rewrite abs-no-dups-p-of-put-assoc-equal)
                        (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-1)
                        (:rewrite abs-fs-p-when-hifat-no-dups-p)
                        (:rewrite hifat-find-file-correctness-1-lemma-1)
                        (:rewrite consp-of-assoc-of-abs-fs-fix)
                        (:rewrite abs-file->contents-when-m1-file-p)
                        (:rewrite subsetp-when-prefixp)))
       :induct (mv (fat32-filename-list-prefixp path relpath)
                   (addrs-at fs relpath))
       :expand ((:free (fs) (addrs-at fs relpath))
                (abs-disassoc fs path new-index))))))

  (defthm
    addrs-at-of-abs-disassoc-1
    (equal (addrs-at (mv-nth 1 (abs-disassoc fs path new-index))
                     relpath)
           (cond ((or (equal (mv-nth 1 (abs-disassoc fs path new-index))
                             (abs-fs-fix fs))
                      (not (fat32-filename-list-prefixp path relpath)))
                  (addrs-at (abs-fs-fix fs) relpath))
                 ((fat32-filename-list-equiv relpath path)
                  (list (nfix new-index)))
                 (t nil)))
    :hints
    (("goal"
      :use (:instance lemma (new-index (nfix new-index)))))))

(defthm ctx-app-ok-of-abs-disassoc-1
  (implies
   ;; This clause becomes a test for path's existence...
   (not (equal (mv-nth 1 (abs-disassoc fs path new-index))
               (abs-fs-fix fs)))
   (ctx-app-ok (mv-nth 1 (abs-disassoc fs path new-index))
               new-index path))
  :hints (("goal" :in-theory (enable ctx-app-ok))))

(defthm abs-mkdir-correctness-lemma-12
  (equal (frame->frame (put-assoc-equal 0 val frame))
         (frame->frame frame))
  :hints (("goal" :do-not-induct t
           :in-theory (enable frame->frame))))

(defthm
  abs-mkdir-correctness-lemma-2
  (equal (frame-val->path (cdr (assoc-equal 0 (frame-with-root root frame))))
         nil)
  :hints (("goal" :in-theory (enable frame-with-root))))

(defthmd abs-mkdir-correctness-lemma-3
  (equal (assoc-equal x (frame-with-root root frame))
         (if (equal x 0)
             (cons 0 (frame-val nil (abs-fs-fix root) 0))
             (assoc-equal x frame)))
  :hints (("goal" :in-theory (enable frame-with-root))))

(defthmd abs-mkdir-correctness-lemma-13
  (equal (assoc-equal x (frame->frame frame))
         (if (not (equal x 0))
             (assoc-equal x frame)
             nil))
  :hints (("goal" :in-theory (enable frame->frame))))

(defthm
  abs-mkdir-correctness-lemma-14
  (implies (and (consp (assoc-equal 0 frame))
                (not (consp (assoc-equal x frame))))
           (not (consp (assoc-equal x (partial-collapse frame path)))))
  :hints (("goal" :in-theory (enable partial-collapse collapse-this
                                     abs-mkdir-correctness-lemma-3
                                     abs-mkdir-correctness-lemma-13)
           :induct (partial-collapse frame path))))

(defthm
  abs-mkdir-correctness-lemma-15
  (implies
   (and (equal (frame-val->path (cdr (assoc-equal 0 frame)))
               nil)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0))
   (and
    (equal
     (frame-val->path (cdr (assoc-equal x (partial-collapse frame path))))
     (if (consp (assoc-equal x (partial-collapse frame path)))
         (frame-val->path (cdr (assoc-equal x frame)))
       nil))
    (equal
     (frame-val->src (cdr (assoc-equal x (partial-collapse frame path))))
     (if (consp (assoc-equal x (partial-collapse frame path)))
         (frame-val->src (cdr (assoc-equal x frame)))
       0))))
  :hints (("goal" :in-theory
           (e/d (partial-collapse collapse-this
                                  abs-mkdir-correctness-lemma-3
                                  abs-mkdir-correctness-lemma-13)
                ((:definition remove-assoc-equal)
                 (:rewrite remove-assoc-when-absent-1)
                 (:rewrite remove-assoc-of-put-assoc)
                 (:rewrite subsetp-when-prefixp)
                 (:rewrite abs-fs-fix-when-abs-fs-p)
                 (:rewrite abs-fs-p-when-hifat-no-dups-p)
                 (:definition abs-complete)
                 (:rewrite remove-assoc-of-remove-assoc)
                 (:definition len)))
           :induct (partial-collapse frame path))))

(defthmd
  abs-mkdir-correctness-lemma-16
  (implies (not (consp (dirname path)))
           (equal (dirname path) nil))
  :hints (("goal" :in-theory (enable dirname)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (zp (len (dirname path)))
             (equal (dirname path) nil))
    :hints (("goal" :in-theory (disable len-of-dirname))))))

(defthm abs-mkdir-correctness-lemma-17
  (implies (atom path)
           (equal (abs-find-file-src frame path)
                  0))
  :hints (("goal" :in-theory (enable abs-find-file-src
                                     abs-find-file-helper))))

(defthm
  abs-mkdir-correctness-lemma-18
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (mv-nth 1 (collapse frame))
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame))))
   (hifat-equiv
    (mv-nth 0
            (collapse (partial-collapse frame (dirname path))))
    (mv-nth 0 (collapse frame))))
  :hints
  (("goal" :in-theory (disable (:rewrite partial-collapse-correctness-1 . 1))
    :use (:instance (:rewrite partial-collapse-correctness-1 . 1)
                    (path (dirname path))
                    (frame frame)))))

(defthm
  abs-mkdir-correctness-lemma-20
  (implies
   (not (intersectp-equal y (abs-addrs (abs-fs-fix fs))))
   (not
    (intersectp-equal
     y
     (abs-addrs (remove-assoc-equal (fat32-filename-fix (car path))
                                    (abs-fs-fix fs)))))))

(defthm
  abs-mkdir-correctness-lemma-21
  (implies
   (and (not (member-equal (nfix new-index) y))
        (not (intersectp-equal y (abs-addrs (abs-fs-fix fs)))))
   (not (intersectp-equal
         y
         (abs-addrs (mv-nth 1
                            (abs-disassoc fs path new-index))))))
  :hints (("goal" :in-theory (enable abs-disassoc abs-addrs)
           :induct (abs-disassoc fs path new-index))))

(defthm
  abs-mkdir-correctness-lemma-22
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name fs)))
        (no-duplicatesp-equal (abs-addrs fs)))
   (not (intersectp-equal
         (abs-addrs (remove-assoc-equal name fs))
         (abs-addrs (abs-file->contents (cdr (assoc-equal name fs)))))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-mkdir-correctness-lemma-23
  (implies (and (no-duplicatesp-equal (abs-addrs (abs-fs-fix fs)))
                (not (member-equal (nfix new-index)
                                   (abs-addrs (abs-fs-fix fs)))))
           (no-duplicatesp-equal
            (abs-addrs (mv-nth 1
                               (abs-disassoc fs path new-index)))))
  :hints (("goal" :in-theory (enable abs-disassoc abs-addrs)
           :induct (abs-disassoc fs path new-index))))

(defthm
  abs-mkdir-correctness-lemma-24
  (ctx-app-ok
   (list (find-new-index
          (strip-cars (partial-collapse frame (dirname path)))))
   (find-new-index
    (strip-cars (partial-collapse frame (dirname path))))
   nil)
  :hints (("goal" :in-theory (enable ctx-app-ok addrs-at abs-fs-fix)
           :do-not-induct t)))

(defthm abs-disassoc-of-abs-fs-fix
  (equal (abs-disassoc (abs-fs-fix fs) path new-index)
         (abs-disassoc fs path new-index))
  :hints (("Goal" :in-theory (enable abs-disassoc))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and (abs-fs-p fs) (natp new-index))
      (equal
       (names-at (mv-nth 1 (abs-disassoc fs path new-index))
                 relpath)
       (cond
        ((or
          (equal (mv-nth 1 (abs-disassoc fs path new-index))
                 fs)
          (not (fat32-filename-list-prefixp path relpath)))
         (names-at fs relpath))
        (t nil))))
     :hints
     (("goal"
       :in-theory
       (e/d
        (abs-top-addrs names-at
                       abs-disassoc fat32-filename-list-fix
                       abs-fs-p abs-file-alist-p abs-no-dups-p)
        ((:rewrite abs-fs-p-correctness-1)
         (:rewrite abs-no-dups-p-of-put-assoc-equal)
         (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-1)
         (:rewrite abs-fs-p-when-hifat-no-dups-p)
         (:rewrite hifat-find-file-correctness-1-lemma-1)
         (:rewrite consp-of-assoc-of-abs-fs-fix)
         (:rewrite abs-file->contents-when-m1-file-p)
         (:rewrite subsetp-when-prefixp)
         (:rewrite remove-when-absent)
         (:definition remove-equal)
         (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
         (:rewrite abs-file-alist-p-when-m1-file-alist-p)
         (:rewrite abs-file-alist-p-correctness-1)
         (:rewrite abs-no-dups-p-when-m1-file-alist-p)
         (:rewrite abs-addrs-when-m1-file-alist-p-lemma-2)
         (:rewrite abs-addrs-when-m1-file-alist-p)
         (:rewrite member-of-abs-addrs-when-natp . 2)
         (:rewrite member-of-abs-fs-fix-when-natp)
         (:rewrite abs-file-contents-p-when-m1-file-contents-p)
         (:rewrite fat32-filename-fix-when-fat32-filename-p)))
       :induct (mv (fat32-filename-list-prefixp path relpath)
                   (names-at fs relpath))
       :expand
       ((:free (fs) (names-at fs relpath))
        (abs-disassoc fs path new-index)
        (:with
         abs-file-contents-fix-when-abs-file-contents-p
         (abs-file-contents-fix
          (mv-nth
           1
           (abs-disassoc
            (abs-file->contents
             (cdr
              (assoc-equal (fat32-filename-fix (car path))
                           fs)))
            (cdr path)
            new-index)))))))))

  (defthm
    names-at-of-abs-disassoc-1
    (equal
     (names-at (mv-nth 1 (abs-disassoc fs path new-index))
               relpath)
     (if
      (or (equal (mv-nth 1 (abs-disassoc fs path new-index))
                 (abs-fs-fix fs))
          (not (fat32-filename-list-prefixp path relpath)))
      (names-at fs relpath)
      nil))
    :hints
    (("goal" :use (:instance lemma (fs (abs-fs-fix fs))
                             (new-index (nfix new-index)))))))

(defthm dist-names-of-abs-disassoc-1
  (implies (dist-names fs relpath frame)
           (dist-names (mv-nth 1 (abs-disassoc fs path new-index))
                       relpath frame))
  :hints (("goal" :in-theory (enable dist-names))))

(defthm
  abs-find-file-correctness-lemma-16
  (implies
   (and
    (fat32-filename-list-prefixp x y)
    (zp (mv-nth 1 (abs-find-file-helper fs x)))
    (not
     (consp
      (abs-addrs
       (abs-file->contents (mv-nth 0 (abs-find-file-helper fs x)))))))
   (not (consp (addrs-at fs y))))
  :hints
  (("goal" :in-theory
    (e/d (abs-find-file-helper addrs-at fat32-filename-list-prefixp)
         (ctx-app-ok-when-abs-complete-lemma-4))
    :induct (mv (fat32-filename-list-prefixp x y)
                (mv-nth 0 (abs-find-file-helper fs x))))
   ("subgoal *1/1'''"
    :use
    (:instance
     ctx-app-ok-when-abs-complete-lemma-4
     (fs (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car x))
                                               (abs-fs-fix fs)))))
     (relpath (cdr y))))))

(defthm
  abs-mkdir-correctness-lemma-25
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root frame)
                                         path))
           2)
    (prefixp
     (fat32-filename-list-fix path)
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (equal
     (mv-nth
      1
      (abs-find-file
       (remove-assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))
       path))
     2)
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (m1-regular-file-p (mv-nth 0 (abs-find-file frame path))))
   (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (fat32-filename-list-prefixp-alt ctx-app-ok)
                    (abs-find-file-correctness-lemma-16
                     abs-find-file-of-put-assoc-lemma-7
                     (:rewrite abs-addrs-when-m1-file-alist-p)
                     (:rewrite partial-collapse-correctness-lemma-24)
                     (:definition assoc-equal)
                     (:rewrite remove-when-absent)
                     (:definition remove-equal)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite abs-fs-p-when-hifat-no-dups-p)
                     (:rewrite prefixp-when-equal-lengths)
                     (:rewrite subsetp-when-prefixp)
                     (:definition no-duplicatesp-equal)))
    :use
    ((:instance
      abs-find-file-correctness-lemma-16
      (x
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
        path))
      (y
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (fs
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame))))))
     (:instance
      (:rewrite abs-find-file-of-put-assoc-lemma-6)
      (path path)
      (frame (frame->frame frame))
      (x (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))))))
  :otf-flg t)

(defthm
  abs-mkdir-correctness-lemma-26
  (implies
   (and (consp (assoc-equal 0 frame))
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (mv-nth 1 (collapse frame))
        (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (abs-separate frame))
   (equal
    (m1-regular-file-p (mv-nth 0 (abs-find-file frame path)))
    (m1-regular-file-p (mv-nth 0
                               (hifat-find-file (mv-nth 0 (collapse frame))
                                                path)))))
  :hints
  (("goal"
    :in-theory (e/d ((:definition abs-find-file)
                     collapse (:definition collapse-this)
                     len-of-fat32-filename-list-fix)
                    ((:rewrite partial-collapse-correctness-lemma-24)
                     (:definition remove-equal)
                     (:definition assoc-equal)
                     (:definition remove-assoc-equal)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite nthcdr-when->=-n-len-l)
                     (:rewrite abs-find-file-of-put-assoc-lemma-6)
                     (:rewrite subsetp-when-prefixp)
                     (:definition strip-cars)
                     abs-find-file-helper-of-collapse-3
                     abs-find-file-correctness-1-lemma-3
                     (:rewrite consp-of-nthcdr)
                     (:rewrite abs-find-file-helper-of-collapse-lemma-2)
                     (:rewrite partial-collapse-correctness-lemma-2)
                     (:rewrite put-assoc-equal-without-change . 2)
                     (:rewrite abs-find-file-correctness-lemma-14)
                     (:rewrite prefixp-when-equal-lengths)
                     (:rewrite abs-find-file-correctness-lemma-31)
                     (:definition put-assoc-equal)
                     (:rewrite abs-fs-p-when-hifat-no-dups-p)))
    :induct (collapse frame)
    :expand
    ((:with abs-find-file-of-put-assoc
            (:free (name val frame path)
                   (abs-find-file (put-assoc-equal name val frame)
                                  path)))
     (:with
      abs-find-file-of-remove-assoc-1
      (abs-find-file (remove-assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))
                     path))))
   ("subgoal *1/6.4'" :expand ((:free (x) (hide x))))))

(defthm
  abs-mkdir-correctness-lemma-27
 (implies
  (and (consp (assoc-equal 0 frame))
       (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
       (mv-nth 1 (collapse frame))
       (frame-p frame)
       (no-duplicatesp-equal (strip-cars frame))
       (subsetp-equal (abs-addrs (frame->root frame))
                      (frame-addrs-root (frame->frame frame)))
       (abs-separate frame))
  (equal
   (abs-directory-file-p (mv-nth 0 (abs-find-file frame path)))
   (m1-directory-file-p (mv-nth 0
                                (hifat-find-file (mv-nth 0 (collapse frame))
                                                 path)))))
 :hints
 (("goal"
   :do-not-induct t
   :in-theory
   (e/d
    (abs-file-p-alt)
    (abs-file-p-of-abs-find-file abs-mkdir-correctness-lemma-26
                                 (:rewrite m1-regular-file-p-correctness-1)
                                 m1-directory-file-p-when-m1-file-p))
   :use
   (abs-file-p-of-abs-find-file
    abs-mkdir-correctness-lemma-26
    (:instance (:rewrite m1-regular-file-p-correctness-1)
               (file (mv-nth 0
                             (hifat-find-file (mv-nth 0 (collapse frame))
                                              path))))))
  ("subgoal 1"
   :expand
   (m1-regular-file-p (mv-nth 0
                              (hifat-find-file (mv-nth 0 (collapse frame))
                                               path))))))

(defthm
  abs-mkdir-correctness-lemma-28
  (not
   (intersectp-equal
    (names-at
     (frame-val->dir
      (cdr (assoc-equal 0
                        (partial-collapse frame (dirname path)))))
     nil)
    (names-at
     (list
      (find-new-index
       (strip-cars (partial-collapse frame (dirname path)))))
     nil)))
  :hints (("goal" :in-theory (enable names-at abs-fs-fix)
           :do-not-induct t)))

(defthm abs-mkdir-correctness-lemma-29
  (implies (atom n)
           (dist-names (list n) relpath frame))
  :hints (("goal" :in-theory (enable names-at abs-fs-fix dist-names))))

(defthm abs-mkdir-correctness-lemma-30
  (implies (atom n)
           (equal (names-at (list n) relpath) nil))
  :hints (("goal" :in-theory (enable names-at abs-fs-fix))))

(defthm
  abs-mkdir-correctness-lemma-31
  (equal (collapse (frame-with-root (frame->root frame)
                                    (frame->frame frame)))
         (collapse frame))
  :hints
  (("goal"
    :in-theory
    (e/d (collapse collapse-this)
         ((:rewrite partial-collapse-correctness-lemma-24)
          (:definition no-duplicatesp-equal)
          (:definition assoc-equal)
          (:rewrite subsetp-when-prefixp)
          (:rewrite prefixp-when-equal-lengths)
          (:definition remove-equal)
          (:rewrite strip-cars-of-remove-assoc)
          (:rewrite assoc-after-put-assoc)
          (:rewrite strip-cars-of-put-assoc)
          (:rewrite no-duplicatesp-of-strip-cars-of-frame->frame)
          (:definition remove-assoc-equal)
          (:rewrite remove-when-absent)
          (:rewrite remove-assoc-of-put-assoc)
          (:rewrite remove-assoc-of-remove-assoc)
          abs-separate-of-frame->frame-of-collapse-this-lemma-8))
    :do-not-induct t
    :expand ((collapse frame)
             (collapse (frame-with-root (frame->root frame)
                                        (frame->frame frame))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (collapse-equiv (frame-with-root (frame->root frame)
                                     (frame->frame frame))
                    frame)
    :hints (("Goal" :in-theory (enable collapse-equiv))))))

;; (thm (implies
;;       (and (collapse-equiv frame1 frame2)
;;            (consp (assoc-equal 0 frame1))
;;            (not (consp (frame-val->path (cdr (assoc-equal 0 frame1)))))
;;            (mv-nth 1 (collapse frame1))
;;            (frame-p frame1)
;;            (no-duplicatesp-equal (strip-cars frame1))
;;            (subsetp-equal (abs-addrs (frame->root frame1))
;;                           (frame-addrs-root (frame->frame frame1)))
;;            (abs-separate frame1)
;;            (or
;;             (m1-regular-file-p (mv-nth 0 (abs-find-file frame1 path)))
;;             (abs-complete
;;              (abs-file->contents (mv-nth 0 (abs-find-file frame1 path)))))
;;            (consp (assoc-equal 0 frame2))
;;            (not (consp (frame-val->path (cdr (assoc-equal 0 frame2)))))
;;            (mv-nth 1 (collapse frame2))
;;            (frame-p frame2)
;;            (no-duplicatesp-equal (strip-cars frame2))
;;            (subsetp-equal (abs-addrs (frame->root frame2))
;;                           (frame-addrs-root (frame->frame frame2)))
;;            (abs-separate frame2)
;;            (or
;;             (m1-regular-file-p (mv-nth 0 (abs-find-file frame2 path)))
;;             (abs-complete
;;              (abs-file->contents (mv-nth 0 (abs-find-file frame2 path))))))
;;       (equal (abs-find-file frame1 path)
;;              (abs-find-file frame2 path)))
;;      :hints
;;      (("goal"
;;        :do-not-induct t
;;        :in-theory (e/d
;;                    (collapse-equiv)
;;                    (abs-find-file-correctness-2
;;                     abs-mkdir-correctness-lemma-26))
;;        :use ((:instance
;;               abs-find-file-correctness-2 (frame frame1))
;;              (:instance
;;               abs-find-file-correctness-2 (frame frame2)))))
;;      :otf-flg t)

(defthm
  abs-mkdir-correctness-lemma-32
  (implies (and (mv-nth 1 (collapse frame))
                (atom path))
           (equal (partial-collapse frame path)
                  (if (atom (frame->frame frame))
                      frame
                      (frame-with-root (mv-nth 0 (collapse frame))
                                       nil))))
  :hints
  (("goal"
    :in-theory (e/d (partial-collapse collapse)
                    ((:definition no-duplicatesp-equal)
                     (:rewrite partial-collapse-correctness-lemma-24)
                     (:definition assoc-equal)
                     (:rewrite subsetp-when-prefixp)
                     (:definition true-listp)
                     (:rewrite put-assoc-equal-without-change . 2)
                     abs-separate-of-frame->frame-of-collapse-this-lemma-8
                     (:rewrite true-list-fix-when-true-listp)
                     (:rewrite true-listp-when-string-list)
                     (:definition string-listp)
                     (:definition put-assoc-equal)
                     (:rewrite remove-assoc-of-put-assoc)
                     (:rewrite abs-fs-p-when-hifat-no-dups-p)
                     (:definition remove-assoc-equal)
                     (:definition remove-equal)
                     (:rewrite fat32-filename-p-correctness-1)))
    :induct (collapse frame)
    :expand ((partial-collapse frame path)
             (collapse-this frame
                            (1st-complete (frame->frame frame)))))))

(defthm
  abs-mkdir-correctness-lemma-33
  (implies (natp n)
           (ctx-app-ok (list n) n nil))
  :hints (("goal" :in-theory (enable ctx-app-ok addrs-at abs-fs-fix)
           :do-not-induct t)))

(defthmd abs-mkdir-correctness-lemma-34
  (implies (and (not (null x))
                (atom (remove-assoc-equal x alist))
                (no-duplicatesp-equal (strip-cars alist)))
           (list-equiv alist
                       (if (atom (assoc-equal x alist))
                           nil (list (assoc-equal x alist))))))

(defthmd
  abs-mkdir-correctness-lemma-35
  (implies (and (atom (frame->frame frame))
                (no-duplicatesp-equal (strip-cars frame))
                (consp (assoc-equal 0 frame))
                (equal (frame-val->src (cdr (assoc-equal 0 frame)))
                       0)
                (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
                (frame-p frame))
           (equal (list (cons 0
                              (make-frame-val :dir (frame->root frame)
                                              :src 0
                                              :path nil)))
                  frame))
  :hints (("goal" :in-theory (enable frame->frame frame->root frame-p)
           :do-not-induct t
           :use (:instance abs-mkdir-correctness-lemma-34 (x 0)
                           (alist frame))
           :expand (assoc-equal 0 frame))))

(defthm
  abs-mkdir-correctness-lemma-36
  (implies
   (and (member-equal new-index y)
        (subsetp-equal (abs-addrs (abs-fs-fix fs))
                       y)
        (natp new-index))
   (subsetp-equal (abs-addrs (mv-nth 1 (abs-disassoc fs path new-index)))
                  y))
  :hints (("goal" :in-theory (enable abs-disassoc)
           :expand (abs-addrs (list new-index)))))

(defthm abs-mkdir-correctness-lemma-37
  (implies (not (consp (frame->frame frame)))
           (dist-names (frame->root frame)
                       nil (remove-assoc-equal 0 frame)))
  :hints (("goal" :in-theory (enable frame->frame))))

(defthm abs-mkdir-correctness-lemma-38
  (implies (atom path)
           (equal (abs-find-file-helper fs path)
                  (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm abs-mkdir-correctness-lemma-39
  (implies (atom path)
           (equal (abs-find-file frame path)
                  (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (enable abs-find-file))))

(defthm
  abs-mkdir-correctness-lemma-40
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame))))
   (subsetp-equal
    (abs-addrs
     (frame-val->dir$inline
      (cdr (assoc-equal 0
                        (partial-collapse frame (dirname path))))))
    (frame-addrs-root
     (frame->frame (partial-collapse frame (dirname path))))))
  :hints
  (("goal"
    :do-not-induct t
    :cases
    ((not
      (equal
       (frame-val->dir
        (cdr (assoc-equal 0
                          (partial-collapse frame (dirname path)))))
       (frame->root (partial-collapse frame (dirname path)))))))
   ("subgoal 1" :in-theory (enable frame->root))))

(defthm
  names-at-of-abs-disassoc-lemma-1
  (implies
   (not
    (equal
     (mv-nth
      1
      (abs-disassoc (abs-file->contents
                     (cdr (assoc-equal (fat32-filename-fix (car path))
                                       fs)))
                    (cdr path)
                    new-index))
     (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                           fs)))))
   (not
    (equal
     (put-assoc-equal
      (fat32-filename-fix (car path))
      (abs-file
       (abs-file->dir-ent
        (cdr (assoc-equal (fat32-filename-fix (car path))
                          fs)))
       (mv-nth 1
               (abs-disassoc
                (abs-file->contents
                 (cdr (assoc-equal (fat32-filename-fix (car path))
                                   fs)))
                (cdr path)
                new-index)))
      fs)
     fs)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite put-assoc-equal-without-change . 1))
    :use
    (:instance
     (:rewrite put-assoc-equal-without-change . 1)
     (alist fs)
     (val
      (abs-file
       (abs-file->dir-ent
        (cdr (assoc-equal (fat32-filename-fix (car path))
                          fs)))
       (mv-nth 1
               (abs-disassoc
                (abs-file->contents
                 (cdr (assoc-equal (fat32-filename-fix (car path))
                                   fs)))
                (cdr path)
                new-index))))
     (name (fat32-filename-fix (car path)))))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (abs-fs-p fs)
              (equal (names-at (mv-nth 0 (abs-disassoc fs path new-index))
                               relpath)
                     (if (equal (mv-nth 1 (abs-disassoc fs path new-index))
                                (abs-fs-fix fs))
                         nil
                         (names-at fs (append path relpath)))))
     :hints
     (("goal"
       :in-theory
       (e/d (abs-top-addrs names-at
                           abs-disassoc fat32-filename-list-fix
                           abs-fs-p abs-file-alist-p abs-no-dups-p)
            ((:rewrite abs-fs-p-correctness-1)
             (:rewrite abs-no-dups-p-of-put-assoc-equal)
             (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-1)
             (:rewrite abs-fs-p-when-hifat-no-dups-p)
             (:rewrite hifat-find-file-correctness-1-lemma-1)
             (:rewrite consp-of-assoc-of-abs-fs-fix)
             (:rewrite abs-file->contents-when-m1-file-p)
             (:rewrite subsetp-when-prefixp)
             (:rewrite remove-when-absent)
             (:rewrite absfat-equiv-implies-set-equiv-addrs-at-1-lemma-1)
             (:definition remove-equal)
             (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
             (:rewrite abs-file-alist-p-when-m1-file-alist-p)
             (:rewrite abs-file-alist-p-correctness-1)
             (:rewrite abs-no-dups-p-when-m1-file-alist-p)
             (:rewrite abs-addrs-when-m1-file-alist-p)
             (:rewrite member-of-abs-addrs-when-natp . 2)
             (:rewrite member-of-abs-fs-fix-when-natp)
             (:rewrite abs-file-contents-p-when-m1-file-contents-p)
             (:rewrite fat32-filename-fix-when-fat32-filename-p)))
       :induct (abs-disassoc fs path new-index)
       :expand
       (:with
        (:rewrite put-assoc-equal-without-change . 1)
        (equal
         (put-assoc-equal
          (fat32-filename-fix (car path))
          (abs-file
           (abs-file->dir-ent
            (cdr (assoc-equal (fat32-filename-fix (car path))
                              fs)))
           (mv-nth
            1
            (abs-disassoc
             (abs-file->contents
              (cdr (assoc-equal (fat32-filename-fix (car path))
                                fs)))
             (cdr path)
             new-index)))
          fs)
         fs))))))

  (defthm
    names-at-of-abs-disassoc-2
    (equal (names-at (mv-nth 0 (abs-disassoc fs path new-index)) relpath)
           (if (equal (mv-nth 1 (abs-disassoc fs path new-index)) (abs-fs-fix fs))
               nil
             (names-at fs (append path relpath))))
    :hints
    (("goal"
      :use
      (:instance
       lemma
       (fs (abs-fs-fix fs)))))))

;; I regard both of the following rewrite rules as dangerous, so I'm keeping
;; them disabled except for where they're needed.
(defthmd frame->frame-of-put-assoc
  (equal (frame->frame (put-assoc-equal key val frame))
         (if (equal 0 key)
             (frame->frame frame)
             (put-assoc-equal key val (frame->frame frame))))
  :hints (("goal" :in-theory (enable frame->frame))))
(defthm frame->root-of-put-assoc
  (equal (frame->root (put-assoc-equal key val frame))
         (if (equal 0 key)
             (frame-val->dir val)
             (frame->root frame)))
  :hints (("goal" :in-theory (enable frame->root))))

(defthm
  abs-mkdir-correctness-lemma-41
  (implies (not (zp (abs-find-file-src frame path)))
           (consp (assoc-equal (abs-find-file-src frame path)
                               (frame->frame frame))))
  :hints
  (("goal" :in-theory (e/d (frame->frame)
                           ((:rewrite abs-find-file-src-correctness-1)))
    :use (:rewrite abs-find-file-src-correctness-1))))

(defthm
  abs-mkdir-correctness-lemma-42
  (implies
   (not (consp (assoc-equal x (frame->frame frame))))
   (not
    (consp (assoc-equal x
                        (frame->frame (partial-collapse frame path))))))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthm
  abs-mkdir-correctness-lemma-43
  (implies
   (consp (assoc-equal x
                       (frame->frame (partial-collapse frame path))))
   (and
    (equal
     (frame-val->src
      (cdr (assoc-equal x
                        (frame->frame (partial-collapse frame path)))))
     (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (equal
     (frame-val->path
      (cdr (assoc-equal x
                        (frame->frame (partial-collapse frame path)))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthm
  abs-mkdir-correctness-lemma-44
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (abs-separate frame)
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (not
     (equal 0
            (abs-find-file-src
             (partial-collapse frame (dirname path))
             (dirname path)))))
   (subsetp-equal
    (abs-addrs
     (frame->root (partial-collapse frame (dirname path))))
    (frame-addrs-root
     (put-assoc-equal
      (abs-find-file-src
       (partial-collapse frame (dirname path))
       (dirname path))
      (frame-val
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src
           (partial-collapse frame (dirname path))
           (dirname path))
          frame)))
       (mv-nth
        1
        (abs-disassoc
         (frame-val->dir
          (cdr
           (assoc-equal
            (abs-find-file-src
             (partial-collapse frame (dirname path))
             (dirname path))
            (partial-collapse frame (dirname path)))))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (abs-find-file-src
               (partial-collapse frame (dirname path))
               (dirname path))
              frame))))
          (dirname path))
         (find-new-index
          (strip-cars
           (partial-collapse frame (dirname path))))))
       (frame-val->src
        (cdr
         (assoc-equal
          (abs-find-file-src
           (partial-collapse frame (dirname path))
           (dirname path))
          frame))))
      (frame->frame
       (partial-collapse frame (dirname path)))))))
  :hints
  (("goal"
    :cases
    ((not
      (and
       (consp
        (assoc-equal
         (abs-find-file-src
          (partial-collapse frame (dirname path))
          (dirname path))
         (frame->frame
          (partial-collapse frame (dirname path)))))
       (equal
        (frame-val->src
         (frame-val
          (frame-val->path
           (cdr
            (assoc-equal
             (abs-find-file-src
              (partial-collapse frame (dirname path))
              (dirname path))
             frame)))
          (mv-nth
           1
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src
                (partial-collapse frame (dirname path))
                (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src
                  (partial-collapse frame (dirname path))
                  (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars
              (partial-collapse frame (dirname path))))))
          (frame-val->src
           (cdr
            (assoc-equal
             (abs-find-file-src
              (partial-collapse frame (dirname path))
              (dirname path))
             frame)))))
        (frame-val->src
         (cdr
          (assoc-equal
           (abs-find-file-src
            (partial-collapse frame (dirname path))
            (dirname path))
           (frame->frame
            (partial-collapse frame (dirname path))))))))))
    :do-not-induct t)
   ("subgoal 1" :in-theory (enable frame->frame))))

(defthm
  abs-mkdir-correctness-lemma-45
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (abs-separate frame))
   (dist-names
    (frame-val->dir$inline
     (cdr (assoc-equal 0
                       (partial-collapse frame (dirname path)))))
    nil
    (frame->frame (partial-collapse frame (dirname path)))))
  :hints
  (("goal"
    :cases
    ((not
      (equal
       (frame-val->dir
        (cdr (assoc-equal 0
                          (partial-collapse frame (dirname path)))))
       (frame->root (partial-collapse frame (dirname path)))))))
   ("subgoal 1" :in-theory (enable frame->root))))

(defthm
  abs-mkdir-correctness-lemma-46
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (abs-separate frame)
    (not
     (equal
      0
      (abs-find-file-src (partial-collapse frame (dirname path))
                         (dirname path)))))
   (dist-names
    (frame-val->dir$inline
     (cdr
      (assoc-equal
       (abs-find-file-src (partial-collapse frame (dirname path))
                          (dirname path))
       (partial-collapse frame (dirname path)))))
    (frame-val->path$inline
     (cdr
      (assoc-equal
       (abs-find-file-src (partial-collapse frame (dirname path))
                          (dirname path))
       frame)))
    (remove-assoc-equal
     (abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path))
     (frame->frame (partial-collapse frame (dirname path))))))
  :hints
  (("goal"
    :in-theory (e/d (frame->frame)
                    (abs-separate-of-frame->frame-of-collapse-this-lemma-2))
    :use
    (:instance
     abs-separate-of-frame->frame-of-collapse-this-lemma-2
     (x (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path)))
     (frame
      (frame->frame (partial-collapse frame (dirname path))))))))

(defthm
  abs-mkdir-correctness-lemma-47
  (implies
   (and (zp (mv-nth 1 (abs-find-file-helper fs path)))
        (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs path)))
        (not (member-equal (nfix new-index)
                           (abs-addrs (abs-fs-fix fs)))))
   (not (equal (mv-nth 1 (abs-disassoc fs path new-index))
               (abs-fs-fix fs))))
  :hints
  (("goal"
    :in-theory
    (e/d (abs-find-file-helper abs-disassoc fat32-filename-list-fix)
         (ctx-app-ok-when-abs-complete-lemma-2 nfix))
    :expand
    ((:with
      put-assoc-equal-without-change
      (equal
       (put-assoc-equal
        (car path)
        (abs-file (abs-file->dir-ent (cdr (assoc-equal (car path) fs)))
                  (list (nfix new-index)))
        fs)
       fs))
     (abs-disassoc fs path new-index)
     (abs-file-contents-fix (list (nfix new-index))))
    :induct (abs-find-file-helper fs path))
   ("subgoal *1/1"
    :use (:instance ctx-app-ok-when-abs-complete-lemma-2
                    (name (fat32-filename-fix (car path))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (zp (mv-nth 1 (abs-find-file-helper fs path)))
          (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs path)))
          (not (member-equal (nfix new-index)
                             (abs-addrs (abs-fs-fix fs))))
          (abs-fs-p fs))
     (not (equal (mv-nth 1 (abs-disassoc fs path new-index))
                 fs))))))

(defthm
  abs-mkdir-correctness-lemma-48
  (implies
   (consp
    (nthcdr
     (len
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame))))
     (dirname path)))
   (not
    (intersectp-equal
     (names-at
      (frame-val->dir
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path)))))
      nil)
     (names-at
      nil
      (cdr
       (nthcdr
        (+ -1 (len path))
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame)))))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite nthcdr-of-nthcdr))
    :use
    (:instance
     (:rewrite nthcdr-of-nthcdr)
     (x
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame))))
     (b (+ -1 (len path)))
     (a 1)))))

(defthm
  abs-mkdir-correctness-lemma-49
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (abs-separate frame)
    (not
     (equal
      0
      (abs-find-file-src (partial-collapse frame (dirname path))
                         (dirname path)))))
   (not
    (intersectp-equal
     (names-at
      (frame-val->dir
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path)))))
      nil)
     (names-at
      (frame->root (partial-collapse frame (dirname path)))
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d nil
                    ((:rewrite abs-separate-correctness-1-lemma-21
                               . 1)))
    :use
    (:instance
     (:rewrite abs-separate-correctness-1-lemma-21 . 1)
     (relpath
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame))))
     (root (frame->root (partial-collapse frame (dirname path))))
     (frame (frame->frame (partial-collapse frame (dirname path))))
     (x (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path)))))
   ("subgoal 2" :in-theory (enable frame->frame))
   ("subgoal 1" :in-theory (enable frame->frame))))

(defthm
  abs-place-file-helper-of-ctx-app-1
  (implies
   (and (abs-fs-p (mv-nth 0
                          (abs-place-file-helper fs path file)))
        (ctx-app-ok abs-file-alist1 x x-path)
        (not (member-equal (fat32-filename-fix (car path))
                           (names-at abs-file-alist1 x-path)))
        (abs-fs-p (ctx-app abs-file-alist1 fs x x-path)))
   (equal
    (ctx-app abs-file-alist1
             (mv-nth 0
                     (abs-place-file-helper fs path file))
             x x-path)
    (if (consp path)
        (mv-nth 0
                (abs-place-file-helper (ctx-app abs-file-alist1 fs x x-path)
                                       (append x-path path)
                                       file))
        (ctx-app abs-file-alist1 fs x x-path))))
  :hints
  (("goal" :in-theory
    (e/d (abs-place-file-helper ctx-app ctx-app-ok addrs-at names-at)
         ((:rewrite abs-file-alist-p-correctness-1)
          (:rewrite hifat-equiv-when-absfat-equiv)
          (:definition no-duplicatesp-equal)
          (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-1)
          (:rewrite subsetp-when-prefixp)
          (:rewrite abs-addrs-when-m1-file-alist-p)
          (:rewrite abs-addrs-of-ctx-app-2)))
    :induct (mv (append x-path path)
                (ctx-app abs-file-alist1 fs x x-path))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (abs-fs-p (mv-nth 0
                            (abs-place-file-helper fs path file)))
          (ctx-app-ok abs-file-alist1 x x-path)
          (not (member-equal (fat32-filename-fix (car path))
                             (names-at abs-file-alist1 x-path)))
          (abs-fs-p (ctx-app abs-file-alist1 fs x x-path))
          (abs-fs-p fs)
          (abs-complete fs)
          (m1-file-p file))
     (equal
      (ctx-app abs-file-alist1
               (mv-nth 0 (hifat-place-file fs path file))
               x x-path)
      (if (consp path)
          (mv-nth 0
                  (abs-place-file-helper (ctx-app abs-file-alist1 fs x x-path)
                                         (append x-path path)
                                         file))
          (ctx-app abs-file-alist1 fs x x-path)))))))

(defthmd abs-place-file-helper-of-fat32-filename-list-fix
  (equal
   (abs-place-file-helper fs (fat32-filename-list-fix path) file)
   (abs-place-file-helper fs path file))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(defcong
  fat32-filename-list-equiv
  equal
  (abs-place-file-helper fs path file)
  2
  :hints (("Goal" :use
           (abs-place-file-helper-of-fat32-filename-list-fix
            (:instance
             abs-place-file-helper-of-fat32-filename-list-fix
             (path path-equiv))))))

(defthm
  abs-place-file-helper-of-ctx-app-lemma-1
  (implies (>= (nfix n) (len l))
           (fat32-filename-equiv (nth n l) nil)))

(defthm abs-mkdir-correctness-lemma-50
  (implies (consp path)
           (fat32-filename-list-equiv
            (append (dirname path)
                    (list (basename path)))
            path))
  :hints (("goal" :in-theory (enable dirname basename
                                     basename-dirname-helper
                                     fat32-filename-list-fix
                                     fat32-filename-list-equiv)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (iff (fat32-filename-list-equiv (dirname path)
                                    path)
         (atom path))
    :instructions
    ((:bash ("goal" :in-theory (enable dirname basename
                                       basename-dirname-helper
                                       fat32-filename-list-fix
                                       fat32-filename-list-equiv)))
     (:claim
      (equal
       (len (append (fat32-filename-list-fix path)
                    (list (mv-nth 0
                                  (basename-dirname-helper path)))))
       (len path))
      :hints :none)
     (:change-goal nil t)
     (:dive 1 1)
     := :up
     (:rewrite len-of-fat32-filename-list-fix)
     :top
     :s :bash))))

(defthm
  abs-mkdir-correctness-lemma-52
  (implies
   (and
    (not (consp (abs-addrs (frame-val->dir (cdr (assoc-equal 0 frame))))))
    (not (consp (dirname path)))
    (not (consp (assoc-equal (basename path)
                             (frame-val->dir (cdr (assoc-equal 0 frame)))))))
   (not (equal (mv-nth 1
                       (hifat-find-file (frame->root frame)
                                        path))
               0)))
  :hints
  (("goal"
    :in-theory (e/d (hifat-find-file fat32-filename-list-fix frame->root)
                    (abs-mkdir-correctness-lemma-50))
    :do-not-induct t
    :use abs-mkdir-correctness-lemma-50
    :expand (fat32-filename-list-fix path))))

(defthm
  abs-mkdir-correctness-lemma-53
  (implies
   (and
    (not
     (equal
      0
      (abs-find-file-src (partial-collapse frame (dirname path))
                         (dirname path))))
    (consp (assoc-equal 0 frame)))
   (consp (frame->frame frame)))
  :hints
  (("goal"
    :in-theory (e/d (collapse frame->frame)
                    ((:rewrite abs-find-file-src-correctness-1)
                     (:rewrite consp-of-remove-assoc-1)))
    :do-not-induct t
    :use
    ((:instance (:rewrite abs-find-file-src-correctness-1)
                (path (dirname path))
                (frame (partial-collapse frame (dirname path))))
     (:instance
      (:rewrite consp-of-remove-assoc-1)
      (alist frame)
      (x2 0)
      (x1 (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path)))))))
  :rule-classes
  ((:forward-chaining
    :trigger-terms
    ((abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path))))))

(defthm
  abs-mkdir-correctness-lemma-54
  (implies
   (and
    (not
     (equal
      0
      (abs-find-file-src (partial-collapse frame (dirname path))
                         (dirname path))))
    (mv-nth 1 (collapse frame))
    (consp (assoc-equal 0 frame)))
   (< '0
      (1st-complete (frame->frame frame))))
  :hints (("goal" :in-theory (enable collapse)
           :do-not-induct t))
  :rule-classes
  ((:forward-chaining
    :trigger-terms
    ((abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path))))
   :linear))

(defthm
  abs-mkdir-correctness-lemma-55
  (implies
   (not
    (equal
     0
     (abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path))))
   (not
    (equal
     (abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path))
     (find-new-index
      (strip-cars (partial-collapse frame (dirname path)))))))
  :instructions
  ((:use
    (:instance
     (:rewrite find-new-index-correctness-1)
     (fd-list
      (strip-cars (partial-collapse frame (dirname path))))))
   :split (:contrapose 1)
   (:dive 1)
   := :up (:rewrite member-of-strip-cars)
   (:rewrite abs-find-file-src-correctness-1)))

(defthm
  abs-mkdir-correctness-lemma-56
  (equal (consp (assoc-equal x
                             (mv-nth 0
                                     (abs-disassoc fs path new-index))))
         (if (member-equal x (names-at fs path))
             t nil))
  :hints (("goal" :in-theory (enable abs-disassoc names-at)
           :induct (abs-disassoc fs path new-index))))

(defthm
  absfat-subsetp-of-put-assoc-3
  (implies
   (and (abs-file-alist-p abs-file-alist1)
        (abs-no-dups-p abs-file-alist1)
        (absfat-subsetp (remove-assoc name abs-file-alist1)
                        abs-file-alist2)
        (m1-regular-file-p (cdr (assoc-equal name abs-file-alist2)))
        (fat32-filename-p name)
        (m1-regular-file-p val)
        (equal (abs-file->contents val)
               (abs-file->contents (cdr (assoc-equal name abs-file-alist2)))))
   (absfat-subsetp (put-assoc-equal name val abs-file-alist1)
                   abs-file-alist2))
  :hints (("goal" :in-theory (e/d (absfat-subsetp abs-no-dups-p) nil)
           :induct (put-assoc-equal name val abs-file-alist1))
          ("subgoal *1/2" :expand (abs-no-dups-p abs-file-alist1))))

(defthm
  abs-mkdir-correctness-lemma-58
  (implies
   (and (absfat-subsetp abs-file-alist1 abs-file-alist2)
        (abs-file-alist-p abs-file-alist1)
        (consp (assoc-equal x abs-file-alist1))
        (not (abs-directory-file-p (cdr (assoc-equal x abs-file-alist1)))))
   (not (abs-directory-file-p (cdr (assoc-equal x abs-file-alist2)))))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm
  abs-mkdir-correctness-lemma-59
  (implies
   (and
    (not (abs-fs-p (abs-file->contents
                    (cdr (assoc-equal (fat32-filename-fix (car path))
                                      fs1)))))
    (abs-fs-p fs1)
    (absfat-subsetp fs1 fs2))
   (not (abs-directory-file-p
         (cdr (assoc-equal (fat32-filename-fix (car path))
                           fs2)))))
  :hints (("goal" :in-theory (disable (:rewrite abs-mkdir-correctness-lemma-58))
           :use (:instance (:rewrite abs-mkdir-correctness-lemma-58)
                           (abs-file-alist2 fs2)
                           (x (fat32-filename-fix (car path)))
                           (abs-file-alist1 fs1)))))

(defthm
  abs-mkdir-correctness-lemma-62
  (implies
   (and
    (absfat-subsetp
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs1)))
              (cdr path)
              file))
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file)))
    (m1-regular-file-p file))
   (absfat-subsetp
    (mv-nth '0
            (abs-place-file-helper
             (abs-file->contents$inline
              (cdr (assoc-equal (fat32-filename-fix (car path))
                                fs1)))
             (cdr path)
             file))
    (abs-file-contents-fix
     (mv-nth '0
             (abs-place-file-helper
              (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file))))))

(defthm
  abs-mkdir-correctness-lemma-63
  (implies
   (and
    (absfat-subsetp
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs1)))
              (cdr path)
              file))
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file)))
    (abs-directory-file-p file))
   (absfat-subsetp
    (mv-nth '0
            (abs-place-file-helper
             (abs-file->contents$inline
              (cdr (assoc-equal (fat32-filename-fix (car path))
                                fs1)))
             (cdr path)
             file))
    (abs-file-contents-fix
     (mv-nth '0
             (abs-place-file-helper
              (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file))))))

(defthm
  abs-mkdir-correctness-lemma-64
  (implies
   (not
    (absfat-subsetp
     (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                           fs1)))
     (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                           fs2)))))
   (consp (assoc-equal (fat32-filename-fix (car path))
                       fs1)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (abs-place-file-helper absfat-subsetp abs-file-p-alt)
                    nil))))

(defthm
  abs-mkdir-correctness-lemma-65
  (implies
   (and
    (abs-directory-file-p
     (cdr (assoc-equal (fat32-filename-fix (car path))
                       fs2)))
    (abs-fs-p fs1)
    (absfat-subsetp fs1 fs2)
    (not (abs-directory-file-p
          (cdr (assoc-equal (fat32-filename-fix (car path))
                            fs1)))))
   (absfat-subsetp
    fs1
    (put-assoc-equal
     (fat32-filename-fix (car path))
     (abs-file
      (abs-file->dir-ent
       (cdr (assoc-equal (fat32-filename-fix (car path))
                         fs2)))
      (mv-nth
       0
       (abs-place-file-helper
        (abs-file->contents
         (cdr (assoc-equal (fat32-filename-fix (car path))
                           fs2)))
        (cdr path)
        file)))
     fs2)))
  :hints
  (("goal"
    :in-theory (e/d (abs-place-file-helper absfat-subsetp abs-file-p-alt)
                    ((:rewrite abs-mkdir-correctness-lemma-58)))
    :use (:instance (:rewrite abs-mkdir-correctness-lemma-58)
                    (abs-file-alist2 fs2)
                    (x (fat32-filename-fix (car path)))
                    (abs-file-alist1 fs1)))))

(defthm
  abs-mkdir-correctness-lemma-66
  (implies
   (and
    (absfat-subsetp
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs1)))
              (cdr path)
              file))
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file)))
    (m1-regular-file-p file))
   (absfat-subsetp
    (abs-file-contents-fix
     (mv-nth '0
             (abs-place-file-helper
              (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs1)))
              (cdr path)
              file)))
    (abs-file-contents-fix
     (mv-nth '0
             (abs-place-file-helper
              (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file)))))
  :hints
  (("goal"
    :in-theory (e/d (abs-place-file-helper absfat-subsetp abs-file-p-alt)))))

(defthm
  abs-mkdir-correctness-lemma-67
  (implies
   (and
    (absfat-subsetp
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs1)))
              (cdr path)
              file))
     (mv-nth 0
             (abs-place-file-helper
              (abs-file->contents
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file)))
    (abs-directory-file-p file))
   (absfat-subsetp
    (abs-file-contents-fix
     (mv-nth '0
             (abs-place-file-helper
              (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs1)))
              (cdr path)
              file)))
    (abs-file-contents-fix
     (mv-nth '0
             (abs-place-file-helper
              (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car path))
                                 fs2)))
              (cdr path)
              file)))))
  :hints
  (("goal"
    :in-theory (e/d (abs-place-file-helper absfat-subsetp abs-file-p-alt))
    :do-not-induct t)))

(defthm
  abs-mkdir-correctness-lemma-57
  (implies
   (and (abs-fs-p fs1)
        (abs-fs-p fs2)
        (absfat-subsetp fs1 fs2)
        (abs-file-p file)
        (abs-no-dups-p (abs-file->contents file))
        (zp (mv-nth 1
                    (abs-place-file-helper fs2 path file))))
   (absfat-subsetp (mv-nth 0
                           (abs-place-file-helper fs1 path file))
                   (mv-nth 0
                           (abs-place-file-helper fs2 path file))))
  :hints (("goal" :in-theory (enable abs-place-file-helper
                                     absfat-subsetp abs-file-p-alt)
           :induct (mv (abs-place-file-helper fs1 path file)
                       (abs-place-file-helper fs2 path file)))))

(defthmd
  abs-mkdir-correctness-lemma-61
  (implies (not (or (equal (mv-nth 1
                                   (abs-place-file-helper fs path file))
                           *enospc*)
                    (equal (mv-nth 1
                                   (abs-place-file-helper fs path file))
                           *enotdir*)
                    (equal (mv-nth 1
                                   (abs-place-file-helper fs path file))
                           *enoent*)))
           (equal (mv-nth 1
                          (abs-place-file-helper fs path file))
                  0))
  :hints (("goal" :in-theory (enable abs-place-file-helper))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and
       (equal (mv-nth 1
                      (abs-place-file-helper fs2 path file))
              28)
       (abs-fs-p fs1)
       (abs-fs-p fs2))
      (> (mv-nth 1
                 (abs-place-file-helper fs1 path file))
         2))
     :hints
     (("goal"
       :in-theory (enable abs-place-file-helper
                          absfat-subsetp abs-file-p-alt)
       :do-not-induct t
       :induct (mv (abs-place-file-helper fs1 path file)
                   (abs-place-file-helper fs2 path file))))
     :rule-classes :linear))

  (defthm
    abs-mkdir-correctness-lemma-68
    (implies
     (and
      (equal (mv-nth 1
                     (abs-place-file-helper fs2 path file))
             28))
     (> (mv-nth 1
                (abs-place-file-helper fs1 path file))
        2))
    :hints (("goal" :use (:instance lemma (fs1 (abs-fs-fix fs1))
                                    (fs2 (abs-fs-fix fs2)))))
    :rule-classes :linear))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and
       (equal (mv-nth 1
                      (abs-place-file-helper fs2 path file))
              *enoent*)
       (abs-fs-p fs1)
       (abs-fs-p fs2)
       (absfat-subsetp fs2 fs1))
      (> (mv-nth 1
                 (abs-place-file-helper fs1 path file))
         0))
     :hints
     (("goal"
       :in-theory (enable abs-place-file-helper
                          absfat-subsetp abs-file-p-alt)
       :induct (mv (abs-place-file-helper fs1 path file)
                   (abs-place-file-helper fs2 path file))))
     :rule-classes :linear))

  (defthm
    abs-mkdir-correctness-lemma-69
    (implies
     (and
      (equal (mv-nth 1
                     (abs-place-file-helper fs2 path file))
             *enoent*)
      (absfat-subsetp (abs-fs-fix fs2)
                      (abs-fs-fix fs1)))
     (> (mv-nth 1
                (abs-place-file-helper fs1 path file))
        0))
    :hints (("goal" :use (:instance lemma (fs1 (abs-fs-fix fs1))
                                    (fs2 (abs-fs-fix fs2)))))
    :rule-classes :linear))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (equal (mv-nth 1
                                  (abs-place-file-helper fs2 path file))
                          *enotdir*)
                   (abs-fs-p fs1)
                   (absfat-subsetp (abs-fs-fix fs1)
                                   (abs-fs-fix fs2))
                   (not (abs-directory-file-p file)))
              (equal (mv-nth 1
                             (abs-place-file-helper fs1 path file))
                     *enotdir*))
     :hints (("goal" :in-theory (enable abs-place-file-helper
                                        absfat-subsetp abs-file-p-alt)
              :induct (mv (abs-place-file-helper fs1 path file)
                          (abs-place-file-helper fs2 path file))))))

  (defthm
    abs-mkdir-correctness-lemma-70
    (implies (and (equal (mv-nth 1
                                 (abs-place-file-helper fs2 path file))
                         *enotdir*)
                  (absfat-subsetp (abs-fs-fix fs1)
                                  (abs-fs-fix fs2))
                  (case-split (not (abs-directory-file-p file))))
             (equal (mv-nth 1
                            (abs-place-file-helper fs1 path file))
                    *enotdir*))
    :hints (("goal" :use (:instance lemma (fs1 (abs-fs-fix fs1)))))))

(defthm
  abs-mkdir-correctness-lemma-71
  (implies
   (and (absfat-equiv fs1 fs2)
        (syntaxp (not (term-order fs1 fs2)))
        (or (abs-directory-file-p
             (cdr (assoc-equal (fat32-filename-fix (car path))
                               fs1)))
            (abs-directory-file-p
             (cdr (assoc-equal (fat32-filename-fix (car path))
                               fs2))))
        (abs-fs-p fs1)
        (abs-fs-p fs2))
   (absfat-equiv
    (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                          fs1)))
    (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                          fs2)))))
  :hints (("goal" :in-theory (enable absfat-equiv)
           :do-not-induct t)))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (equal (mv-nth 1
                                  (abs-place-file-helper fs2 path file))
                          *enotdir*)
                   (abs-fs-p fs1)
                   (abs-fs-p fs2)
                   (absfat-equiv fs1 fs2)
                   (abs-directory-file-p file))
              (equal (mv-nth 1
                             (abs-place-file-helper fs1 path file))
                     *enotdir*))
     :hints
     (("goal"
       :in-theory
       (e/d (abs-place-file-helper abs-file-p-alt)
            ((:rewrite absfat-equiv-implies-set-equiv-names-at-1-lemma-4)
             (:rewrite
              absfat-equiv-implies-set-equiv-addrs-at-1-lemma-2)
             (:definition put-assoc-equal)
             (:rewrite abs-file-alist-p-correctness-1)
             (:rewrite
              hifat-find-file-correctness-1-lemma-1)
             (:definition abs-complete)
             (:rewrite
              abs-fs-fix-of-put-assoc-equal-lemma-1)
             (:rewrite subsetp-when-prefixp)
             abs-mkdir-correctness-lemma-71))
       :induct (mv (abs-place-file-helper fs1 path file)
                   (abs-place-file-helper fs2 path file)))
      ("subgoal *1/3"
       :use
       (abs-mkdir-correctness-lemma-71
        (:instance (:rewrite absfat-equiv-implies-set-equiv-names-at-1-lemma-3)
                   (abs-file-alist2 fs1)
                   (abs-file-alist1 fs2)
                   (x (fat32-filename-fix (car path))))))
      ("subgoal *1/1"
       :use
       (abs-mkdir-correctness-lemma-71
        (:instance (:rewrite absfat-equiv-implies-set-equiv-names-at-1-lemma-3)
                   (abs-file-alist2 fs1)
                   (abs-file-alist1 fs2)
                   (x (fat32-filename-fix (car path)))))))))

  (defthm
    abs-mkdir-correctness-lemma-72
    (implies (and (equal (mv-nth 1
                                 (abs-place-file-helper fs2 path file))
                         *enotdir*)
                  (absfat-equiv fs1 fs2)
                  (abs-directory-file-p file))
             (equal (mv-nth 1
                            (abs-place-file-helper fs1 path file))
                    *enotdir*))
    :hints (("goal" :use (:instance lemma (fs1 (abs-fs-fix fs1))
                                    (fs2 (abs-fs-fix fs2)))))))

;; This theorem reminds me of one more reason why no duplication should be
;; allowed. List lengths have to be the same!
(defthm
  abs-mkdir-correctness-lemma-60
  (implies (and (absfat-equiv fs1 fs2)
                (abs-file-p file)
                (abs-no-dups-p (abs-file->contents file)))
           (and
            (absfat-equiv (mv-nth 0
                                  (abs-place-file-helper fs1 path file))
                          (mv-nth 0
                                  (abs-place-file-helper fs2 path file)))
            (equal (mv-nth 1
                           (abs-place-file-helper fs1 path file))
                   (mv-nth 1
                           (abs-place-file-helper fs2 path file)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (absfat-equiv)
                    (abs-mkdir-correctness-lemma-57
                     (:rewrite abs-place-file-helper-correctness-2)))
    :use ((:instance abs-mkdir-correctness-lemma-57
                     (fs1 (abs-fs-fix fs1))
                     (fs2 (abs-fs-fix fs2)))
          (:instance abs-mkdir-correctness-lemma-57
                     (fs1 (abs-fs-fix fs2))
                     (fs2 (abs-fs-fix fs1)))
          (:instance (:rewrite abs-place-file-helper-correctness-2)
                     (file file)
                     (path path)
                     (fs fs1))
          (:instance (:rewrite abs-place-file-helper-correctness-2)
                     (file file)
                     (path path)
                     (fs fs2))
          (:instance (:rewrite abs-mkdir-correctness-lemma-61)
                     (file file)
                     (path path)
                     (fs fs1))
          (:instance (:rewrite abs-mkdir-correctness-lemma-61)
                     (file file)
                     (path path)
                     (fs fs2)))))
  :otf-flg t)

(defthm collapse-hifat-place-file-lemma-1
  (implies (stringp x)
           (not (ctx-app-ok x var relpath)))
  :hints (("goal" :in-theory (enable ctx-app-ok)))
  :rule-classes (:type-prescription :rewrite))

(defthm collapse-hifat-place-file-lemma-3
  (implies (m1-file-alist-p fs)
           (equal (abs-top-addrs fs) nil))
  :hints (("goal" :in-theory (enable abs-top-addrs m1-file-alist-p))))


;; (thm
;;  (implies
;;   (and (consp relpath)
;;        (consp (assoc-equal name
;;                            fs))
;;        (abs-file-alist-p
;;         (cdr (caddr (assoc-equal name
;;                                  (abs-fs-fix fs)))))
;;        (m1-file-alist-p fs))
;;   (m1-file-alist-p
;;    (cdr (caddr (assoc-equal name
;;                             (abs-fs-fix fs))))))
;;  :hints (("goal" :in-theory (e/d
;;                              (m1-file-alist-p abs-fs-fix m1-directory-file-p
;;                                               m1-file->contents abs-file)
;;                              ((:REWRITE ABS-FS-P-CORRECTNESS-1)(:REWRITE ABS-FS-P-WHEN-HIFAT-NO-DUPS-P)(:REWRITE
;;                                                                                                         ABS-ADDRS-WHEN-M1-FILE-ALIST-P-LEMMA-2)(:DEFINITION LEN)(:REWRITE
;;                                                                                                         M1-FILE-ALIST-P-OF-M1-FILE->CONTENTS)(:REWRITE M1-FILE-FIX-WHEN-M1-FILE-P))))))

;; (thm (implies (m1-file-alist-p fs) (equal (addrs-at fs relpath) nil)) :hints
;;      (("GOal" :in-theory (enable addrs-at m1-file-alist-p abs-directory-file-p abs-file->contents))))

(defthm collapse-hifat-place-file-lemma-2
  (implies
   (path-clear path frame)
   (path-clear path (remove-assoc-equal x frame)))
  :hints (("goal" :in-theory (enable path-clear))))

(defthmd
  collapse-hifat-place-file-lemma-4
  (implies
   (and
    (zp
     (mv-nth
      1
      (abs-find-file-helper fs
                            (mv-nth 1
                                    (basename-dirname-helper path)))))
    (abs-directory-file-p
     (mv-nth
      0
      (abs-find-file-helper fs
                            (mv-nth 1
                                    (basename-dirname-helper path)))))
    (not (equal (mv-nth 1 (abs-find-file-helper fs path))
                0)))
   (equal (mv-nth 1 (abs-find-file-helper fs path))
          *enoent*))
  :hints
  (("goal" :in-theory (enable abs-find-file-helper
                              basename-dirname-helper))
   ("subgoal *1/2'''" :expand (basename-dirname-helper (cdr path)))))

(defthm
  collapse-hifat-place-file-lemma-5
  (implies (and (consp x)
                (fat32-filename-list-prefixp x y)
                (equal (mv-nth 1 (abs-find-file-helper fs x))
                       *enoent*))
           (equal (addrs-at fs y) nil))
  :hints
  (("goal" :in-theory
    (e/d (abs-find-file-helper addrs-at fat32-filename-list-prefixp)
         (ctx-app-ok-when-abs-complete-lemma-4))
    :induct (mv (fat32-filename-list-prefixp x y)
                (mv-nth 0 (abs-find-file-helper fs x))))))

(defthm
  collapse-hifat-place-file-lemma-6
  (implies (and (consp x)
                (fat32-filename-list-prefixp x y)
                (equal (mv-nth 1 (abs-find-file-helper fs x))
                       *enoent*))
           (not (ctx-app-ok fs var y)))
  :hints
  (("goal" :in-theory (enable ctx-app-ok))))

(defthm
  collapse-hifat-place-file-lemma-9
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root frame2)
                                         (dirname path)))
           0)
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root frame2)
                                         path))
           2)
    (prefixp
     (fat32-filename-list-fix path)
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1))))))
   (not
    (ctx-app-ok
     (frame->root frame2)
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file-helper dirname
                                          basename-dirname-helper
                                          fat32-filename-list-prefixp-alt)
                    ((:rewrite collapse-hifat-place-file-lemma-6)))
    :use
    (:instance
     (:rewrite collapse-hifat-place-file-lemma-6)
     (y
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1)))))
     (var (1st-complete (frame->frame frame1)))
     (fs (frame->root frame2))
     (x path)))))

(defthm
  collapse-hifat-place-file-lemma-10
  (implies (and (m1-file-p file)
                (hifat-no-dups-p (m1-file->contents file)))
           (abs-no-dups-p (m1-file->contents file)))
  :hints
  (("goal" :in-theory (e/d (m1-file-p m1-file->contents
                                      m1-file-contents-p abs-no-dups-p)
                           ((:rewrite abs-no-dups-p-when-m1-file-alist-p)))
    :use (:instance (:rewrite abs-no-dups-p-when-m1-file-alist-p)
                    (fs (abs-file->contents file))))))

(defthm
  collapse-hifat-place-file-lemma-12
  (implies
   (and (m1-file-p file)
        (hifat-no-dups-p (m1-file->contents file)))
   (not
    (ctx-app-ok
     (m1-file->contents file)
     (1st-complete (frame->frame frame1))
     (nthcdr
      (len path)
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1))))))))
  :hints
  (("goal" :in-theory (disable (:rewrite m1-directory-file-p-when-m1-file-p))
    :use (:instance (:rewrite m1-directory-file-p-when-m1-file-p)
                    (x file)))))

(defthm
  collapse-hifat-place-file-lemma-11
  (implies
   (and
    (equal (frame->root frame1)
           (mv-nth 0
                   (abs-place-file-helper (frame->root frame2)
                                          path file)))
    (m1-file-p file)
    (hifat-no-dups-p (m1-file->contents file))
    (not
     (ctx-app-ok
      (frame->root frame2)
      (1st-complete (frame->frame frame1))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1)))))))
   (not
    (ctx-app-ok
     (frame->root frame1)
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite ctx-app-ok-of-abs-place-file-helper-1))
    :use
    (:instance
     (:rewrite ctx-app-ok-of-abs-place-file-helper-1)
     (x-path
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1)))))
     (x (1st-complete (frame->frame frame1)))
     (file file)
     (path path)
     (fs (frame->root frame2))))))

(defthm
  collapse-hifat-place-file-lemma-7
  (implies
   (and
    (equal (frame->root frame1)
           (mv-nth 0
                   (abs-place-file-helper (frame->root frame2)
                                          path file)))
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root frame2)
                                         (dirname path)))
           0)
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root frame2)
                                         path))
           2)
    (m1-file-p file)
    (hifat-no-dups-p (m1-file->contents file)))
   (equal
    (ctx-app-ok
     (frame->root frame1)
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))
    (ctx-app-ok
     (frame->root frame2)
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite ctx-app-ok-of-abs-place-file-helper-1))
    :use
    (:instance
     (:rewrite ctx-app-ok-of-abs-place-file-helper-1)
     (x-path
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1)))))
     (x (1st-complete (frame->frame frame1)))
     (file file)
     (path path)
     (fs (frame->root frame2))))))

(defthm
  collapse-hifat-place-file-lemma-14
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file-helper (frame->root frame2)
                                         path))
           2)
    (ctx-app-ok
     (frame->root frame2)
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))
    (prefixp
     (fat32-filename-list-fix path)
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1))))))
   (not (equal (mv-nth 1
                       (abs-place-file-helper (frame->root frame2)
                                              path file))
               0)))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file-helper dirname
                                          basename-dirname-helper
                                          fat32-filename-list-prefixp-alt))
    :expand ((abs-place-file-helper (frame->root frame1)
                                    path file)
             (abs-place-file-helper (frame->root frame2)
                                    path file)))))

(defthm
  collapse-hifat-place-file-lemma-13
  (implies
   (and (equal (frame->root frame1)
               (mv-nth 0
                       (abs-place-file-helper (frame->root frame2)
                                              path file)))
        (equal (mv-nth 1
                       (abs-find-file-helper (frame->root frame2)
                                             path))
               2)
        (m1-file-p file)
        (hifat-no-dups-p (m1-file->contents file)))
   (equal
    (ctx-app-ok
     (frame->root frame1)
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))
    (ctx-app-ok
     (frame->root frame2)
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))))
  :instructions
  ((:bash
    ("goal"
     :in-theory (disable (:rewrite ctx-app-ok-of-abs-place-file-helper-1))
     :use
     (:instance
      (:rewrite ctx-app-ok-of-abs-place-file-helper-1)
      (x-path
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                          (frame->frame frame1)))))
      (x (1st-complete (frame->frame frame1)))
      (file file)
      (path path)
      (fs (frame->root frame2)))))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (abs-fs-p fs)
                   (prefixp (fat32-filename-list-fix x)
                            (fat32-filename-list-fix y))
                   (not (consp (names-at fs x))))
              (not (consp (names-at fs y))))
     :hints (("goal" :in-theory (e/d (names-at)
                                     ((:rewrite member-of-remove)))
              :induct (mv (fat32-filename-list-prefixp x y)
                          (names-at fs x)) :expand (names-at fs y))
             ("subgoal *1/1''" :use (:instance (:rewrite member-of-remove)
                                               (x (strip-cars fs))
                                               (b nil)
                                               (a (fat32-filename-fix (car y))))))))

  (defthm
    names-at-when-prefixp
    (implies (and (prefixp (fat32-filename-list-fix x)
                           (fat32-filename-list-fix y))
                  (not (consp (names-at fs x))))
             (not (consp (names-at fs y))))
    :hints (("goal" :use (:instance lemma (fs (abs-fs-fix fs)))))))

(defthm
  path-clear-when-prefixp-lemma-1
  (implies
   (and
    (prefixp (frame-val->path (cdr (car frame)))
             (fat32-filename-list-fix y))
    (prefixp (fat32-filename-list-fix x)
             (fat32-filename-list-fix y))
    (not (prefixp (fat32-filename-list-fix x)
                  (frame-val->path (cdr (car frame)))))
    (not (consp (names-at (frame-val->dir (cdr (car frame)))
                          (nthcdr (len (frame-val->path (cdr (car frame))))
                                  x)))))
   (not (consp (names-at (frame-val->dir (cdr (car frame)))
                         (nthcdr (len (frame-val->path (cdr (car frame))))
                                 y)))))
  :hints
  (("goal"
    :in-theory (e/d nil
                    ((:rewrite prefixp-nthcdr-nthcdr)
                     (:rewrite names-at-when-prefixp)
                     len-when-prefixp))
    :use ((:instance (:rewrite names-at-when-prefixp)
                     (y (nthcdr (len (frame-val->path (cdr (car frame))))
                                y))
                     (fs (frame-val->dir (cdr (car frame))))
                     (x (nthcdr (len (frame-val->path (cdr (car frame))))
                                x)))
          (:instance (:rewrite prefixp-nthcdr-nthcdr)
                     (l2 (fat32-filename-list-fix y))
                     (l1 (fat32-filename-list-fix x))
                     (n (len (frame-val->path (cdr (car frame))))))
          (:instance len-when-prefixp
                     (x (frame-val->path (cdr (car frame))))
                     (y (fat32-filename-list-fix y)))))))

(defthm
  path-clear-when-prefixp-lemma-2
  (implies (not (consp (names-at (frame-val->dir (cdr (car frame)))
                                 nil)))
           (not (consp (names-at (frame-val->dir (cdr (car frame)))
                                 (nthcdr (len x) y)))))
  :hints
  (("goal" :in-theory (e/d (names-at)
                           ((:rewrite member-of-remove)))
    :do-not-induct t
    :expand (names-at (frame-val->dir (cdr (car frame)))
                      (nthcdr (len x) y))
    :use (:instance (:rewrite member-of-remove)
                    (x (strip-cars (frame-val->dir (cdr (car frame)))))
                    (b nil)
                    (a (fat32-filename-fix (nth (len x) y)))))))

(defthm
  path-clear-when-prefixp
  (implies (and (prefixp (fat32-filename-list-fix x)
                         (fat32-filename-list-fix y))
                (path-clear x frame))
           (path-clear y frame))
  :hints
  (("goal"
    :in-theory (e/d (path-clear)
                    (len-when-prefixp (:rewrite prefixp-when-equal-lengths))))
   ("subgoal *1/4'''" :use ((:instance (:rewrite prefixp-when-equal-lengths)
                                       (y (fat32-filename-list-fix y))
                                       (x (fat32-filename-list-fix x)))
                            (:instance len-when-prefixp
                                       (x (fat32-filename-list-fix x))
                                       (y (fat32-filename-list-fix y)))
                            (:instance len-when-prefixp
                                       (x (fat32-filename-list-fix y))
                                       (y (fat32-filename-list-fix x)))))))

(defthm collapse-hifat-place-file-lemma-15
  (implies (and (equal (frame->frame frame1)
                       (frame->frame frame2))
                (equal (frame->root frame1)
                       (frame->root frame2))
                (syntaxp (not (term-order frame1 frame2))))
           (equal (collapse-this frame1 x)
                  (collapse-this frame2 x)))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  abs-place-file-helper-of-ctx-app-2
  (implies
   (not (fat32-filename-list-prefixp x-path path))
   (equal
    (mv-nth 1 (abs-place-file-helper
               (ctx-app fs1 fs2 x x-path)
               path file))
    (mv-nth 1 (abs-place-file-helper
               fs1
               path file))))
  :hints (("Goal" :in-theory (enable abs-place-file-helper ctx-app)
           :induct (mv (fat32-filename-list-prefixp x-path path)
                       (ctx-app fs1 fs2 x x-path)))))

;; Here's the problem with this theorem: it doesn't work for the arbitrary
;; place-file because it can literally dump a number of names in different
;; directories while wiping out a bunch of others, making an utter mess of
;; dist-names and therefor abs-separate. In actual system calls, we create one
;; new name at a time, which is what makes it possible to ensure that we can
;; use path-clear and basically account for everything. But... how do we
;; pass on that kind of stipulation here? It would be nice to hang on to a
;; model where we just do put-assoc and we can tell what the names in each
;; directory are, but when in the middle of collapsing that assumption
;; disappears because wherever you did the put-assoc, that's going somewhere,
;; and then somewhere else, and at various points it sinks deeper and deeper
;; down into the directory tree. So how do we say that we are only introducing
;; this one name? Maybe the answer is simply to maintain path-clear...
(encapsulate
  ()

  (local
   (defun
       induction-scheme (frame1 frame2)
     (declare (xargs :verify-guards nil
                     :measure (len (frame->frame frame1))))
     (cond
      ((and
        (not (atom (frame->frame frame1)))
        (not (zp (1st-complete (frame->frame frame1))))
        (not
         (zp
          (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame1))
                             (frame->frame frame1))))))
        (not
         (or
          (equal
           (frame-val->src
            (cdr
             (assoc-equal (1st-complete (frame->frame frame1))
                          (frame->frame frame1))))
           (1st-complete (frame->frame frame1)))
          (atom
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame1))
                           (frame->frame frame1))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame1))
             (frame->frame frame1))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame1))
                           (frame->frame frame1))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame1))
             (frame->frame frame1)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame1))
                            (frame->frame frame1)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame1))
                           (frame->frame frame1))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame1))
             (frame->frame frame1)))))
         (1st-complete (frame->frame frame1))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame1))
                             (frame->frame frame1))))
              (remove-assoc-equal
               (1st-complete (frame->frame frame1))
               (frame->frame frame1))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame1))
                             (frame->frame frame1)))))))
       (induction-scheme
        (collapse-this frame1
                       (1st-complete (frame->frame frame1)))
        (collapse-this frame2
                       (1st-complete (frame->frame frame2)))))
      ((and
        (not (atom (frame->frame frame1)))
        (not (zp (1st-complete (frame->frame frame1))))
        (zp
         (frame-val->src
          (cdr (assoc-equal (1st-complete (frame->frame frame1))
                            (frame->frame frame1)))))
        (ctx-app-ok
         (frame->root frame1)
         (1st-complete (frame->frame frame1))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame1))
                            (frame->frame frame1))))))
       (induction-scheme
        (collapse-this frame1
                       (1st-complete (frame->frame frame1)))
        (collapse-this frame2
                       (1st-complete (frame->frame frame2)))))
      (t (mv frame1 frame2)))))

  (skip-proofs
   (defthmd
     collapse-hifat-place-file-lemma-8
     (implies
      (and
       (equal (frame->frame frame1)
              (frame->frame frame2))
       (equal (frame->root frame1)
              (mv-nth 0
                      (abs-place-file-helper (frame->root frame2)
                                             path file)))
       ;; We're going to need to make some assumptions about
       ;; abs-place-file-helper and where it is called, because currently it has
       ;; the ability to come in and smoosh the directory structure by placing a file
       ;; at an arbitrary place. While it's all very well to think about
       ;; basenames and dirnames and what should and should not exist, perhaps
       ;; we can go for a property I suspect is provided by partial-collapse -
       ;; path-clear...
       (or
        (atom (dirname path))
        (path-clear (dirname path) (frame->frame frame2)))
       (m1-file-p file)
       (hifat-no-dups-p (m1-file->contents file))
       (dist-names (frame->root frame2)
                   nil (frame->frame frame2))
       (abs-separate (frame->frame frame2))
       (frame-p (frame->frame frame2))
       (no-duplicatesp-equal (strip-cars (frame->frame frame2))))
      (and
       (equal
        (mv-nth 0 (collapse frame1))
        (mv-nth
         0
         (abs-place-file-helper (mv-nth 0 (collapse frame2))
                                path file)))
       (equal (mv-nth 1 (collapse frame1))
              (mv-nth 1 (collapse frame2)))))
     :hints
     (("goal"
       :in-theory
       (e/d
        (collapse)
        ((:definition no-duplicatesp-equal)
         (:rewrite partial-collapse-correctness-lemma-24)
         (:definition assoc-equal)
         (:rewrite subsetp-when-prefixp)
         (:rewrite
          abs-separate-of-frame->frame-of-collapse-this-lemma-8
          . 2)
         (:rewrite partial-collapse-correctness-lemma-28)
         (:rewrite nthcdr-when->=-n-len-l)
         (:rewrite strip-cars-of-frame->frame-of-collapse-this)
         (:definition len)
         (:definition remove-equal)
         (:rewrite remove-when-absent)))
       :induct (induction-scheme frame1 frame2)
       :expand (collapse frame2))))))

;; This theorem asserts some things about applying abs-place-file-helper to
;; filesystem instances with holes...
(defthm
  collapse-hifat-place-file-1
  (implies
   (and (or (not (consp (dirname path)))
            (path-clear (dirname path) frame))
        (m1-file-p file)
        (hifat-no-dups-p (m1-file->contents file))
        (dist-names (frame->root (frame-with-root root frame))
                    nil
                    (frame->frame (frame-with-root root frame)))
        (abs-separate (frame->frame (frame-with-root root frame)))
        (frame-p (frame->frame (frame-with-root root frame)))
        (no-duplicatesp-equal
         (strip-cars (frame->frame (frame-with-root root frame)))))
   (and
    (equal
     (mv-nth
      1
      (collapse
       (frame-with-root (mv-nth 0
                                (abs-place-file-helper root path file))
                        frame)))
     (mv-nth 1
             (collapse (frame-with-root root frame))))
    (equal
     (mv-nth
      0
      (collapse
       (frame-with-root (mv-nth 0
                                (abs-place-file-helper root path file))
                        frame)))
     (mv-nth
      0
      (abs-place-file-helper (mv-nth 0
                                     (collapse (frame-with-root root frame)))
                             path file)))))
  :otf-flg t
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance
     (:rewrite collapse-hifat-place-file-lemma-8)
     (frame1
      (frame-with-root (mv-nth 0
                               (abs-place-file-helper root path file))
                       frame))
     (frame2 (frame-with-root root frame))))))

(defthmd abs-find-file-after-abs-mkdir-lemma-1
  (implies (case-split (consp path))
           (fat32-filename-list-equiv (nthcdr (- (len path) 1) path)
                                      (list (basename path))))
  :hints (("goal" :in-theory (enable basename-dirname-helper
                                     fat32-filename-list-equiv basename))))

(defthm fat32-filename-list-fix-when-zp-len
  (implies (zp (len x))
           (equal (fat32-filename-list-fix x) nil))
  :rule-classes :type-prescription)

(defthm prefixp-of-dirname
  (prefixp (dirname path)
           (fat32-filename-list-fix path))
  :hints (("goal" :in-theory (enable dirname
                                     basename-dirname-helper)))
  :rule-classes
  ((:rewrite
    :corollary
    (fat32-filename-list-prefixp (dirname path) path)
    :hints (("Goal" :in-theory (enable fat32-filename-list-prefixp-alt))))
   :rewrite))

(defthmd
  abs-find-file-after-abs-mkdir-lemma-4
  (implies (fat32-filename-list-equiv (list (basename path))
                                      path)
           (fat32-filename-equiv$inline (basename path)
                                        (car path)))
  :hints
  (("goal" :in-theory (e/d (abs-mkdir abs-find-file abs-find-file-helper
                                      abs-find-file-after-abs-mkdir-lemma-1
                                      len-when-consp
                                      fat32-filename-list-fix
                                      fat32-filename-list-equiv
                                      fat32-filename-equiv)
                           (abs-mkdir-correctness-lemma-50
                            (:definition nth)
                            (:definition true-listp)
                            (:definition string-listp)
                            (:rewrite true-listp-when-string-list)
                            (:rewrite fat32-filename-p-correctness-1)))
    :do-not-induct t)))

(defthm
  abs-find-file-after-abs-mkdir-lemma-2
  (implies (equal (list (basename path))
                  (fat32-filename-list-fix path))
           (consp path))
  :hints
  (("goal" :in-theory (e/d (abs-mkdir abs-find-file abs-find-file-helper
                                      abs-find-file-after-abs-mkdir-lemma-1
                                      abs-find-file-after-abs-mkdir-lemma-4
                                      len-when-consp
                                      fat32-filename-list-fix abs-disassoc)
                           (abs-mkdir-correctness-lemma-50
                            (:definition nth)
                            (:definition true-listp)
                            (:definition string-listp)
                            (:rewrite true-listp-when-string-list)
                            (:rewrite fat32-filename-p-correctness-1)))
    :do-not-induct t))
  :rule-classes :forward-chaining)

(defthm abs-find-file-after-abs-mkdir-lemma-3
  (implies (and (consp x)
                (fat32-filename-list-prefixp x y)
                (not (equal (mv-nth 1 (abs-find-file-helper fs y))
                            *enoent*)))
           (not (equal (mv-nth 1 (abs-find-file-helper fs x))
                       *enoent*)))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-after-abs-mkdir-lemma-5
  (implies (and (dist-names (frame->root frame)
                            nil (frame->frame frame))
                (abs-separate (frame->frame frame))
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (frame-p (frame->frame frame)))
           (dist-names (frame->root (partial-collapse frame path))
                       nil
                       (frame->frame (partial-collapse frame path))))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthm
  abs-find-file-after-abs-mkdir-lemma-6
  (implies (and (abs-separate (frame->frame frame))
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (frame-p (frame->frame frame)))
           (abs-separate (frame->frame (partial-collapse frame path))))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthm
  abs-find-file-after-abs-mkdir-lemma-7
  (implies
   (and
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        frame)))
     (dirname path))
    (equal
     (abs-find-file
      (frame->frame (partial-collapse frame (dirname path)))
      (dirname path))
     '(((dir-ent 0 0 0 0 0 0 0 0 0 0 0 0
                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
        (contents))
       2))
    (not (frame-val->path (cdr (assoc-equal 0 frame))))
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not
     (equal
      0
      (abs-find-file-src (partial-collapse frame (dirname path))
                         (dirname path)))))
   (equal
    (abs-find-file-helper
     (frame-val->dir
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        (partial-collapse frame (dirname path)))))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame))))
      (dirname path)))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :in-theory (e/d (frame->frame)
                    (abs-find-file-correctness-lemma-14))
    :use
    ((:instance
      (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
      (path
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))
        (dirname path)))
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (partial-collapse frame (dirname path)))))))
     (:instance
      abs-find-file-correctness-lemma-14
      (x (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path)))
      (frame (frame->frame (partial-collapse frame (dirname path))))
      (path (dirname path)))))))

(defthm
  abs-find-file-after-abs-mkdir-lemma-8
  (implies
   (and
    (not (frame-val->path (cdr (assoc-equal 0 frame))))
    (consp (assoc-equal 0
                        (partial-collapse frame (dirname path))))
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (no-duplicatesp-equal (abs-addrs (frame->root frame)))
    (mv-nth '1 (collapse frame))
    (not
     (equal
      0
      (abs-find-file-src (partial-collapse frame (dirname path))
                         (dirname path))))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (abs-separate (frame->frame frame)))
   (equal (abs-find-file-helper
           (frame->root (partial-collapse frame (dirname path)))
           path)
          (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :in-theory (e/d (abs-mkdir abs-find-file abs-find-file-helper
                               abs-find-file-after-abs-mkdir-lemma-1
                               abs-find-file-after-abs-mkdir-lemma-4
                               len-when-consp fat32-filename-list-fix
                               abs-disassoc abs-fs-fix)
                    (abs-find-file-after-abs-mkdir-lemma-3
                     abs-find-file-src-correctness-2
                     (:definition nth)
                     (:definition true-listp)
                     (:definition string-listp)
                     (:rewrite true-listp-when-string-list)
                     (:rewrite fat32-filename-p-correctness-1)))
    :use
    ((:instance
      abs-find-file-after-abs-mkdir-lemma-3
      (fs (frame->root (partial-collapse frame (dirname path))))
      (x (dirname path))
      (y (fat32-filename-list-fix path)))
     (:instance abs-find-file-src-correctness-2
                (frame (partial-collapse frame (dirname path)))
                (path (dirname path)))
     (:instance
      (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
      (path path)
      (fs (frame->root (partial-collapse frame (dirname path))))))
    :do-not-induct t))
  :otf-flg t)

(defthm
  abs-find-file-after-abs-mkdir-lemma-9
  (implies
   (and (fat32-filename-list-prefixp x y)
        (not (fat32-filename-list-equiv x y))
        (not (equal (mv-nth 1 (abs-disassoc fs x new-index))
                    (abs-fs-fix fs))))
   (equal (abs-find-file-helper (mv-nth 1 (abs-disassoc fs x new-index))
                                y)
          (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (enable abs-find-file-helper
                                     abs-disassoc fat32-filename-list-fix
                                     fat32-filename-list-equiv
                                     fat32-filename-list-prefixp abs-fs-fix)
           :induct (mv (abs-disassoc fs x new-index)
                       (fat32-filename-list-prefixp x y)))))

(defthm
  abs-find-file-after-abs-mkdir-lemma-11
  (implies
   (and
    (equal
     (mv-nth 1
             (abs-find-file (partial-collapse frame (dirname path))
                            (dirname path)))
     0)
    (not (frame-val->path (cdr (assoc-equal 0 frame))))
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-directory-file-p
     (mv-nth 0
             (abs-find-file (partial-collapse frame (dirname path))
                            (dirname path))))
    (equal
     0
     (abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path)))
    (not
     (member-equal
      (find-new-index
       (strip-cars (partial-collapse frame (dirname path))))
      (abs-addrs
       (frame-val->dir
        (cdr
         (assoc-equal 0
                      (partial-collapse frame (dirname path)))))))))
   (not
    (equal
     (mv-nth
      1
      (abs-disassoc
       (frame-val->dir
        (cdr (assoc-equal 0
                          (partial-collapse frame (dirname path)))))
       (dirname path)
       (find-new-index
        (strip-cars (partial-collapse frame (dirname path))))))
     (frame-val->dir
      (cdr
       (assoc-equal 0
                    (partial-collapse frame (dirname path))))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-find-file-src-correctness-2))
    :use
    ((:instance (:rewrite abs-find-file-src-correctness-2)
                (path (dirname path))
                (frame (partial-collapse frame (dirname path))))))))

(defthm
  abs-find-file-after-abs-mkdir-lemma-10
  (implies
   (and
    (equal
     (mv-nth 1
             (abs-find-file (partial-collapse frame (dirname path))
                            (dirname path)))
     0)
    (not (frame-val->path (cdr (assoc-equal 0 frame))))
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-directory-file-p
     (mv-nth 0
             (abs-find-file (partial-collapse frame (dirname path))
                            (dirname path))))
    (equal
     0
     (abs-find-file-src (partial-collapse frame (dirname path))
                        (dirname path)))
    (not
     (member-equal
      (find-new-index
       (strip-cars (partial-collapse frame (dirname path))))
      (abs-addrs
       (frame-val->dir
        (cdr
         (assoc-equal 0
                      (partial-collapse frame (dirname path)))))))))
   (equal
    (abs-find-file-helper
     (mv-nth
      1
      (abs-disassoc
       (frame-val->dir
        (cdr
         (assoc-equal 0
                      (partial-collapse frame (dirname path)))))
       (dirname path)
       (find-new-index
        (strip-cars (partial-collapse frame (dirname path))))))
     path)
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-find-file-after-abs-mkdir-lemma-9))
    :use
    ((:instance
      (:rewrite abs-find-file-after-abs-mkdir-lemma-9)
      (y path)
      (new-index
       (find-new-index
        (strip-cars (partial-collapse frame (dirname path)))))
      (x (dirname path))
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal 0
                      (partial-collapse frame (dirname path)))))))
     (:instance
      (:rewrite abs-find-file-helper-of-ctx-app-lemma-4)
      (path path)
      (fs
       (mv-nth
        1
        (abs-disassoc
         (frame-val->dir
          (cdr
           (assoc-equal
            0
            (partial-collapse frame (dirname path)))))
         (dirname path)
         (find-new-index
          (strip-cars
           (partial-collapse frame (dirname path))))))))))))

(defthm abs-find-file-after-abs-mkdir-lemma-12
  (subsetp-equal (frame-addrs-root frame)
                 (strip-cars frame))
  :hints (("goal" :in-theory (enable frame-addrs-root))))

(defthm
  abs-find-file-after-abs-mkdir-lemma-13
  (implies
   (and
    (mv-nth 1 (collapse frame))
    (not (frame-val->path (cdr (assoc-equal 0 frame))))
    (consp (assoc-equal 0
                        (partial-collapse frame (dirname path))))
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (abs-directory-file-p
     (mv-nth 0
             (abs-find-file (partial-collapse frame (dirname path))
                            (dirname path))))
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame))))
   (not
    (member-equal
     (find-new-index
      (strip-cars (partial-collapse frame (dirname path))))
     (abs-addrs
      (frame-val->dir$inline
       (cdr
        (assoc-equal '0
                     (partial-collapse frame (dirname path)))))))))
  :instructions
  (:promote
   (:dive 1)
   (:rewrite
    (:rewrite subsetp-member . 4)
    ((y (strip-cars (partial-collapse frame (dirname path))))))
   (:change-goal nil t)
   :bash
   (:=
    (frame-val->dir
     (cdr (assoc-equal 0
                       (partial-collapse frame (dirname path)))))
    (frame->root (partial-collapse frame (dirname path)))
    :hints (("goal" :in-theory (enable frame->root))))
   (:rewrite
    subsetp-trans2
    ((y
      (frame-addrs-root
       (frame->frame (partial-collapse frame (dirname path)))))))
   (:change-goal nil t)
   :bash
   :bash
   (:rewrite
    subsetp-trans
    ((y
      (strip-cars
       (frame->frame (partial-collapse frame (dirname path)))))))
   :bash (:bash ("goal" :in-theory (enable frame->frame)))))

(defthm abs-find-file-after-abs-mkdir-lemma-14
  (implies (fat32-filename-list-equiv (list (basename path))
                                      path)
           (equal (fat32-filename-fix (car path))
                  (basename path)))
  :instructions (:promote (:dive 1)
                          (:= path
                              (list (basename path))
                              :equiv fat32-filename-list-equiv$inline)
                          :top :bash))

(defthm
  abs-find-file-after-abs-mkdir-1
  (implies
   (and
    (mv-nth '1 (collapse frame))
    (equal (frame-val->path (cdr (assoc-equal 0 frame)))
           nil)
    (consp (assoc-equal 0
                        (partial-collapse frame (dirname path))))
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame))))
   (b*
       (((mv frame & mkdir-error-code)
         (abs-mkdir frame path)))
     (implies
      (equal mkdir-error-code 0)
      (b*
          (((mv file error-code)
            (abs-find-file frame path)))
        (and (equal error-code 0)
             (m1-file-equiv
              file
              (make-m1-file
               :dir-ent (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                       t))))))))
  :hints
  (("goal" :in-theory (e/d (abs-mkdir abs-find-file abs-find-file-helper
                                      abs-find-file-after-abs-mkdir-lemma-1
                                      abs-find-file-after-abs-mkdir-lemma-4
                                      len-when-consp fat32-filename-list-fix
                                      abs-disassoc abs-fs-fix)
                           (abs-mkdir-correctness-lemma-50
                            (:definition nth)
                            (:definition true-listp)
                            (:definition string-listp)
                            (:rewrite true-listp-when-string-list)
                            (:rewrite fat32-filename-p-correctness-1)
                            (:rewrite abs-find-file-correctness-lemma-2)
                            (:rewrite
                             abs-find-file-helper-when-m1-file-alist-p)
                            (:rewrite abs-disassoc-correctness-1)
                            (:rewrite abs-fs-p-when-hifat-no-dups-p)
                            (:rewrite abs-find-file-correctness-lemma-31)
                            (:rewrite abs-file-alist-p-correctness-1)
                            (:rewrite consp-of-nthcdr)
                            (:rewrite
                             abs-find-file-correctness-1-lemma-18)
                            (:rewrite abs-find-file-correctness-1-lemma-3)
                            (:rewrite
                             abs-find-file-helper-of-collapse-lemma-1)
                            (:definition no-duplicatesp-equal)
                            (:rewrite abs-fs-p-correctness-1)
                            (:definition len)))
    :use abs-mkdir-correctness-lemma-50
    :do-not-induct t))
  :otf-flg t)

;; Taking this together with abs-mkdir-correctness-lemma-47, it can be
;; determined how the abs-disassoc is going to turn out...
(defthm
  abs-mkdir-correctness-lemma-73
  (implies
   (and
    (not (atom path))
    (not
     (and
      (zp (mv-nth 1 (abs-find-file-helper fs path)))
      (abs-directory-file-p (mv-nth 0
                                    (abs-find-file-helper fs path))))))
   (equal (mv-nth 1 (abs-disassoc fs path new-index))
          (abs-fs-fix fs)))
  :hints
  (("goal"
    :in-theory
    (e/d (abs-find-file-helper abs-disassoc fat32-filename-list-fix)
         (ctx-app-ok-when-abs-complete-lemma-2 nfix))
    :expand
    ((:with
      put-assoc-equal-without-change
      (equal
       (put-assoc-equal
        (car path)
        (abs-file (abs-file->dir-ent (cdr (assoc-equal (car path) fs)))
                  (list (nfix new-index)))
        fs)
       fs))
     (abs-disassoc fs path new-index)
     (abs-file-contents-fix (list (nfix new-index))))
    :induct (abs-find-file-helper fs path))))

(defthm
  abs-mkdir-correctness-lemma-74
  (implies
   (prefixp
    (dirname path)
    (frame-val->path
     (cdr
      (assoc-equal
       (abs-find-file-src (partial-collapse frame (dirname path))
                          (dirname path))
       frame))))
   (>=
    (len
     (frame-val->path
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        frame))))
    (+ -1 (len path))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-mkdir-correctness-lemma-73))
    :use
    (:instance
     (:rewrite abs-mkdir-correctness-lemma-73)
     (new-index
      (find-new-index
       (strip-cars (partial-collapse frame (dirname path)))))
     (path (dirname path))
     (fs
      (frame-val->dir
       (cdr
        (assoc-equal 0
                     (partial-collapse frame (dirname path)))))))))
  :rule-classes :linear)

(defthm
  abs-mkdir-correctness-lemma-75
  (implies
   (and
    (not
     (member-equal
      (basename path)
      (names-at
       (frame-val->dir
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (partial-collapse frame (dirname path)))))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))
        (dirname path)))))
    (prefixp
     (dirname path)
     (frame-val->path
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        frame))))
    (member-equal
     (basename path)
     (names-at
      (frame-val->dir
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path)))))
      nil))
    (<=
     (len
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame))))
     (+ -1 (len path))))
   (not
    (equal
     (mv-nth
      1
      (abs-disassoc
       (frame-val->dir
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (partial-collapse frame (dirname path)))))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))
        (dirname path))
       (find-new-index
        (strip-cars (partial-collapse frame (dirname path))))))
     (frame-val->dir
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        (partial-collapse frame (dirname path))))))))
  :hints
  (("goal"
    :in-theory (e/d (names-at)
                    ((:rewrite abs-mkdir-correctness-lemma-47 . 2)))
    :use
    (:instance
     (:rewrite abs-mkdir-correctness-lemma-47 . 2)
     (new-index
      (find-new-index
       (strip-cars (partial-collapse frame (dirname path)))))
     (path
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))
       (dirname path)))
     (fs
      (frame-val->dir
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path))))))))))

(defthm
  abs-mkdir-correctness-lemma-76
  (implies
   (and
    (equal (list (basename path))
           (fat32-filename-list-fix path))
    (not (consp (abs-addrs (frame-val->dir (cdr (assoc-equal 0 frame))))))
    (not (consp (assoc-equal (basename path)
                             (frame-val->dir (cdr (assoc-equal 0 frame)))))))
   (equal
    (mv-nth
     1
     (hifat-place-file (frame->root frame)
                       path
                       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                         (contents))))
    0))
  :instructions
  (:promote
   (:= path
       (list (basename path))
       :equiv fat32-filename-list-equiv$inline)
   (:dive 1 2)
   :x
   :top
   (:bash ("goal" :in-theory (enable fat32-filename-list-fix frame->root)))))

;; How come these two weren't already proven?
(defthm
  abs-mkdir-correctness-lemma-77
  (equal
   (hifat-find-file fs (append x y))
   (cond
    ((atom y) (hifat-find-file fs x))
    ((and (zp (mv-nth 1 (hifat-find-file fs x)))
          (m1-directory-file-p (mv-nth 0 (hifat-find-file fs x))))
     (hifat-find-file (m1-file->contents (mv-nth 0 (hifat-find-file fs x)))
                      y))
    ((zp (mv-nth 1 (hifat-find-file fs x)))
     (mv (m1-file-fix nil) *enotdir*))
    ((atom x) (hifat-find-file fs y))
    (t (hifat-find-file fs x))))
  :hints (("goal" :in-theory (enable hifat-find-file))))
(defthm
  abs-mkdir-correctness-lemma-89
  (equal
   (abs-find-file-helper fs (append x y))
   (cond ((atom y) (abs-find-file-helper fs x))
         ((and (zp (mv-nth 1 (abs-find-file-helper fs x)))
               (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs x))))
          (abs-find-file-helper
           (abs-file->contents (mv-nth 0 (abs-find-file-helper fs x)))
           y))
         ((zp (mv-nth 1 (abs-find-file-helper fs x)))
          (mv (abs-file-fix nil) *enotdir*))
         ((atom x) (abs-find-file-helper fs y))
         (t (abs-find-file-helper fs x))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-mkdir-correctness-lemma-82
  (implies
   (and
    (equal (list (basename path))
           (fat32-filename-list-fix path))
    (not (consp (abs-addrs (frame-val->dir (cdr (assoc-equal 0 frame))))))
    (not (consp (assoc-equal (basename path)
                             (frame-val->dir (cdr (assoc-equal 0 frame)))))))
   (hifat-equiv
    (mv-nth
     0
     (hifat-place-file (frame->root frame)
                       path
                       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                         (contents))))
    (put-assoc-equal (basename path)
                     '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                       (contents))
                     (frame-val->dir (cdr (assoc-equal 0 frame))))))
  :instructions
  (:promote
   (:dive 1)
   (:= path
       (list (basename path))
       :equiv fat32-filename-list-equiv$inline)
   (:dive 2)
   :x
   :top
   (:bash ("goal" :in-theory (enable hifat-place-file
                                     fat32-filename-list-fix frame->root)))))

(defthm abs-mkdir-correctness-lemma-83
  (implies (fat32-filename-list-equiv (list (basename path))
                                      path)
           (consp path))
  :hints (("goal" :in-theory (enable fat32-filename-list-equiv)
           :do-not-induct t))
  :rule-classes :forward-chaining)

;; (defthm
;;   abs-mkdir-correctness-lemma-84
;;   (implies
;;    (and (fat32-filename-list-equiv (list (basename path))
;;                                    path)
;;         (not (consp (abs-addrs (frame->root frame))))
;;         (consp (assoc-equal (basename path)
;;                             (frame-val->dir (cdr (assoc-equal 0 frame))))))
;;    (absfat-equiv
;;     (mv-nth
;;      0
;;      (hifat-place-file (frame->root frame)
;;                        path
;;                        '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
;;                                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
;;                          (contents))))
;;     (frame->root frame)))
;;   :hints (("goal" :in-theory (enable hifat-place-file frame->root))))

;; How come this was not already proven?
(defthm
 abs-mkdir-correctness-lemma-85
 (implies
      (and (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                    (fat32-filename-list-fix path))
           (equal (mv-nth 1 (abs-find-file frame path))
                  *enoent*))
      (equal (abs-find-file-helper
                  (frame-val->dir (cdr (assoc-equal x frame)))
                  (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                          path))
             (abs-find-file frame path)))
 :hints (("goal" :in-theory (enable abs-find-file hifat-find-file))))

(defthm
  abs-mkdir-correctness-lemma-86
  (implies
   (and
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (prefixp
     (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                        frame)))
     (fat32-filename-list-fix path))
    (nat-equiv
     n
     (len
      (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                         frame))))))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (abs-find-file-src frame path)
                                       frame)))
     (nthcdr
      n
      path))
    (abs-find-file frame path)))
  :hints (("goal" :in-theory (e/d ()
                                  (abs-find-file-src-correctness-2 nfix nat-equiv))
           :use abs-find-file-src-correctness-2
           :do-not-induct t)))

(defthm
  abs-mkdir-correctness-lemma-87
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (not (zp (abs-find-file-src frame path))))
   (prefixp
    (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                       frame)))
    (fat32-filename-list-fix path)))
  :hints (("goal" :in-theory (enable abs-find-file-src))))

(defthmd
  abs-mkdir-correctness-lemma-88
  (implies
   (fat32-filename-p x)
   (iff (member-equal x (names-at fs relpath))
        (zp (mv-nth 1
                    (abs-find-file-helper fs (append relpath (list x)))))))
  :hints (("goal" :in-theory (enable names-at abs-find-file-helper))))

(defthm abs-mkdir-correctness-lemma-90
  (implies (fat32-filename-list-equiv (list (basename path))
                                      path)
           (not (consp (cdr path))))
  :hints (("goal" :in-theory (enable fat32-filename-list-equiv)))
  :rule-classes :forward-chaining)

(defthm
  abs-mkdir-correctness-lemma-91
  (implies
   (and
    (fat32-filename-list-equiv (list (basename path))
                               path)
    (not (consp (abs-addrs (frame-val->dir (cdr (assoc-equal 0 frame))))))
    (not (consp (assoc-equal (basename path)
                             (frame-val->dir (cdr (assoc-equal 0 frame)))))))
   (equal
    (mv-nth
     1
     (hifat-place-file (frame->root frame)
                       path
                       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                         (contents))))
    0))
  :hints (("goal" :in-theory (enable hifat-place-file frame->root))))

(defthm
  abs-mkdir-correctness-lemma-92
  (implies (consp (assoc-equal (basename path)
                               (frame-val->dir (cdr (assoc-equal 0 frame)))))
           (consp (assoc-equal (basename path)
                               (frame->root frame))))
  :hints (("goal" :in-theory (enable frame->root))))

(defthm
  abs-mkdir-correctness-lemma-93
  (implies
   (and
    (not
     (equal
      (mv-nth
       1
       (abs-disassoc
        (frame-val->dir
         (cdr
          (assoc-equal 0
                       (partial-collapse frame (dirname path)))))
        (dirname path)
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path))))))
      (frame-val->dir
       (cdr
        (assoc-equal 0
                     (partial-collapse frame (dirname path)))))))
    (consp (dirname path)))
   (and
    (zp
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr (assoc-equal 0
                          (partial-collapse frame (dirname path)))))
       (dirname path))))
    (abs-directory-file-p
     (mv-nth
      0
      (abs-find-file-helper
       (frame-val->dir
        (cdr (assoc-equal 0
                          (partial-collapse frame (dirname path)))))
       (dirname path))))))
  :instructions (:promote (:contrapose 1)
                          (:dive 1)
                          (:rewrite abs-mkdir-correctness-lemma-73)
                          :top :bash)
  :rule-classes :forward-chaining)

(defthm
  abs-mkdir-correctness-lemma-94
  (implies
   (and
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        frame)))
     (dirname path))
    (<= 0 (+ -1 (len path)))
    (<=
     (+ -1 (len path))
     (len
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame))))))
   (ctx-app-ok
    (list
     (find-new-index
      (strip-cars (partial-collapse frame (dirname path)))))
    (find-new-index
     (strip-cars (partial-collapse frame (dirname path))))
    (nthcdr
     (len
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         frame))))
     (dirname path))))
  :hints (("goal" :in-theory (disable (:rewrite nthcdr-when->=-n-len-l))
           :use (:instance (:rewrite nthcdr-when->=-n-len-l)
                           (l (dirname path))
                           (n (+ -1 (len path)))))))

(defthm
  abs-mkdir-correctness-lemma-95
  (implies
   (and (zp (mv-nth 1 (hifat-find-file fs x)))
        (m1-directory-file-p (mv-nth 0 (hifat-find-file fs x))))
   (equal
    (hifat-place-file fs (append x y) file)
    (if
        (consp y)
        (mv
         (mv-nth
          0
          (hifat-place-file
           fs x
           (make-m1-file
            :contents
            (mv-nth 0
                    (hifat-place-file
                     (m1-file->contents (mv-nth 0 (hifat-find-file fs x)))
                     y file))
            :dir-ent (m1-file->dir-ent (mv-nth 0 (hifat-find-file fs x))))))
         (mv-nth
          1
          (hifat-place-file (m1-file->contents (mv-nth 0 (hifat-find-file fs x)))
                            y file)))
      (hifat-place-file fs x file))))
  :hints
  (("goal"
    :in-theory (enable hifat-place-file hifat-find-file)
    :induct
    (mv
     (mv-nth
      0
      (hifat-place-file
       fs x
       (m1-file
        (m1-file->dir-ent (mv-nth 0 (hifat-find-file fs x)))
        (mv-nth 0
                (hifat-place-file
                 (m1-file->contents (mv-nth 0 (hifat-find-file fs x)))
                 y file)))))
     (append x y)
     (mv-nth 0 (hifat-find-file fs x))))))

(defthm
  abs-mkdir-correctness-lemma-96
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (mv-nth 1 (collapse frame))
    (abs-separate frame)
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (m1-directory-file-p (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  (dirname path))))
    (not
     (abs-directory-file-p
      (mv-nth
       0
       (hifat-find-file
        (mv-nth 0
                (collapse (partial-collapse frame (dirname path))))
        (dirname path))))))
   (equal
    (mv-nth
     1
     (hifat-place-file (mv-nth 0 (collapse frame))
                       path
                       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                         (contents))))
    0))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-mkdir-correctness-lemma-95))
    :use (:instance (:rewrite abs-mkdir-correctness-lemma-95)
                    (file '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                            (contents)))
                    (y (list (basename path)))
                    (x (dirname path))
                    (fs (mv-nth 0 (collapse frame)))))))

(defthm abs-mkdir-correctness-lemma-97
  (implies (not (consp path))
           (equal (dirname path) nil))
  :hints (("goal" :in-theory (enable dirname
                                     basename-dirname-helper)))
  :rule-classes :type-prescription)

(defthm
  abs-mkdir-correctness-lemma-98
  (implies
   (and (hifat-equiv (mv-nth 0 (collapse frame))
                     fs)
        (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (mv-nth 1 (collapse frame))
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (m1-directory-file-p
         (mv-nth 0
                 (hifat-find-file fs (dirname path)))))
   (m1-directory-file-p
    (mv-nth
     '0
     (hifat-find-file
      (mv-nth '0
              (collapse (partial-collapse frame (dirname path))))
      (dirname path))))))

(defthm abs-mkdir-correctness-lemma-99
  (implies (and (hifat-equiv fs1 fs2)
                (syntaxp (not (term-order fs1 fs2)))
                (fat32-filename-p name)
                (m1-file-alist-p fs1)
                (m1-file-alist-p fs2)
                (hifat-no-dups-p fs1)
                (hifat-no-dups-p fs2))
           (iff (consp (assoc-equal name fs1))
                (consp (assoc-equal name fs2))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable hifat-equiv))))

(defthm
  abs-mkdir-correctness-lemma-100
  (implies (consp (assoc-equal name fs))
           (consp (assoc-equal (fat32-filename-fix name)
                               (hifat-file-alist-fix fs))))
  :hints (("goal" :in-theory (enable hifat-file-alist-fix)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (implies (and (fat32-filename-p name)
                           (consp (assoc-equal name fs)))
                      (consp (assoc-equal name (hifat-file-alist-fix fs)))))))

(defthm
  abs-mkdir-correctness-lemma-102
  (implies
   (and (hifat-equiv (mv-nth 0 (collapse frame))
                     fs)
        (m1-directory-file-p
         (mv-nth 0
                 (hifat-find-file fs (dirname path)))))
   (m1-directory-file-p (mv-nth 0
                                (hifat-find-file (mv-nth 0 (collapse frame))
                                                 (dirname path))))))

(defthm
  abs-mkdir-correctness-lemma-101
  (implies
   (and (hifat-equiv (mv-nth 0 (collapse frame))
                     fs)
        (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (mv-nth 1 (collapse frame))
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (m1-directory-file-p
         (mv-nth 0
                 (hifat-find-file fs (dirname path))))
        (equal (mv-nth 1
                       (hifat-find-file fs (dirname path)))
               0))
   (hifat-equiv
    (m1-file->contents
     (mv-nth
      0
      (hifat-find-file
       (mv-nth 0
               (collapse (partial-collapse frame (dirname path))))
       (dirname path))))
    (m1-file->contents
     (mv-nth 0
             (hifat-find-file fs (dirname path))))))
  :hints
  (("goal"
    :use
    (:instance
     hifat-find-file-correctness-4
     (m1-file-alist2 (mv-nth 0 (collapse frame)))
     (m1-file-alist1
      (mv-nth 0
              (collapse (partial-collapse frame (dirname path)))))
     (path (dirname path))))))

(defthm
  abs-mkdir-correctness-lemma-103
  (implies
   (and (hifat-equiv (mv-nth 0 (collapse frame))
                     fs)
        (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (mv-nth 1 (collapse frame))
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (m1-directory-file-p
         (mv-nth 0
                 (hifat-find-file fs (dirname path))))
        (equal (mv-nth 1
                       (hifat-find-file fs (dirname path)))
               0))
   (iff
    (consp
     (assoc-equal
      (basename path)
      (m1-file->contents
       (mv-nth
        0
        (hifat-find-file
         (mv-nth 0
                 (collapse (partial-collapse frame (dirname path))))
         (dirname path))))))
    (consp (assoc-equal
            (basename path)
            (m1-file->contents
             (mv-nth 0
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path))))))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    ((:instance
      abs-mkdir-correctness-lemma-99
      (name (basename path))
      (fs1
       (m1-file->contents
        (mv-nth
         0
         (hifat-find-file
          (mv-nth
           0
           (collapse (partial-collapse frame (dirname path))))
          (dirname path)))))
      (fs2 (m1-file->contents
            (mv-nth 0
                    (hifat-find-file (mv-nth 0 (collapse frame))
                                     (dirname path))))))))))

(defthm
  abs-mkdir-correctness-lemma-104
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (mv-nth 1 (collapse frame))
    (abs-separate frame)
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (m1-directory-file-p (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  (dirname path)))))
   (abs-directory-file-p
    (mv-nth
     0
     (hifat-find-file
      (mv-nth 0
              (collapse (partial-collapse frame (dirname path))))
      (dirname path)))))
  :hints
  (("goal"
    :in-theory (e/d (hifat-place-file)
                    ((:rewrite partial-collapse-correctness-1 . 1)))
    :use ((:instance (:rewrite partial-collapse-correctness-1 . 1)
                     (path (dirname path))
                     (frame frame)))
    :expand
    (:with
     (:rewrite hifat-equiv-when-absfat-equiv)
     (absfat-equiv
      (mv-nth 0
              (collapse (partial-collapse frame (dirname path))))
      fs))
    :do-not-induct t)))

(defthm
  abs-mkdir-correctness-lemma-105
  (implies
   (and
    (m1-directory-file-p (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  (dirname path))))
    (consp path)
    (equal (mv-nth 1
                   (hifat-find-file (mv-nth 0 (collapse frame))
                                    (dirname path)))
           0))
   (equal
    (hifat-place-file (mv-nth 0 (collapse frame))
                      path
                      '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                        (contents)))
    (mv
     (mv-nth
      0
      (hifat-place-file
       (mv-nth 0 (collapse frame))
       (dirname path)
       (m1-file
        (m1-file->dir-ent (mv-nth 0
                                  (hifat-find-file (mv-nth 0 (collapse frame))
                                                   (dirname path))))
        (mv-nth 0
                (hifat-place-file
                 (m1-file->contents
                  (mv-nth 0
                          (hifat-find-file (mv-nth 0 (collapse frame))
                                           (dirname path))))
                 (list (basename path))
                 '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                            0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                   (contents)))))))
     (mv-nth
      1
      (hifat-place-file
       (m1-file->contents (mv-nth 0
                                  (hifat-find-file (mv-nth 0 (collapse frame))
                                                   (dirname path))))
       (list (basename path))
       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
         (contents)))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-mkdir-correctness-lemma-95))
    :use (:instance (:rewrite abs-mkdir-correctness-lemma-95)
                    (file '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                            (contents)))
                    (y (list (basename path)))
                    (x (dirname path))
                    (fs (mv-nth 0 (collapse frame)))))))

(defthm
  abs-mkdir-correctness-lemma-106
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (mv-nth 1 (collapse frame))
    (abs-separate frame)
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (m1-directory-file-p (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  (dirname path))))
    (equal (mv-nth 1
                   (hifat-find-file (mv-nth 0 (collapse frame))
                                    (dirname path)))
           0))
   (iff
    (consp
     (assoc-equal
      (basename path)
      (abs-file->contents
       (mv-nth
        0
        (hifat-find-file
         (mv-nth
          0
          (collapse (partial-collapse frame (dirname path))))
         (dirname path))))))
    (consp
     (assoc-equal (basename path)
                  (m1-file->contents
                   (mv-nth 0
                           (hifat-find-file (mv-nth 0 (collapse frame))
                                            (dirname path))))))))
  :hints
  (("goal"
    :in-theory (e/d (hifat-place-file)
                    ((:rewrite partial-collapse-correctness-1 . 1)))
    :use ((:instance (:rewrite partial-collapse-correctness-1 . 1)
                     (path (dirname path))
                     (frame frame)))
    :expand
    (:with
     (:rewrite hifat-equiv-when-absfat-equiv)
     (absfat-equiv
      (mv-nth 0
              (collapse (partial-collapse frame (dirname path))))
      fs))
    :do-not-induct t)))

(defthm abs-mkdir-correctness-lemma-108
  (equal (nthcdr (+ -1 (len path))
                 (dirname path))
         nil)
  :hints (("goal" :in-theory (e/d nil (len-of-dirname))
           :use len-of-dirname)))

(defthm
  abs-mkdir-correctness-lemma-122
  (implies
   (and (m1-directory-file-p
         (mv-nth 0
                 (hifat-find-file fs (dirname path))))
        (consp path)
        (equal (mv-nth 1
                       (hifat-find-file fs (dirname path)))
               0))
   (equal (hifat-find-file fs path)
          (hifat-find-file
           (m1-file->contents
            (mv-nth 0
                    (hifat-find-file fs (dirname path))))
           (list (basename path)))))
  :hints
  (("goal" :in-theory (disable (:rewrite abs-mkdir-correctness-lemma-77))
    :use (:instance (:rewrite abs-mkdir-correctness-lemma-77)
                    (y (list (basename path)))
                    (x (dirname path))
                    (fs fs)))))

(defthm
  abs-mkdir-correctness-lemma-123
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (m1-file-alist-p fs)
        (mv-nth 1 (collapse frame))
        (hifat-equiv (mv-nth 0 (collapse frame))
                     fs)
        (abs-separate frame)
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (equal (mv-nth 1
                       (hifat-find-file fs (dirname path)))
               0)
        (m1-directory-file-p
         (mv-nth 0
                 (hifat-find-file fs (dirname path)))))
   (iff
    (consp
     (assoc-equal (basename path)
                  (m1-file->contents
                   (mv-nth 0
                           (hifat-find-file (mv-nth 0 (collapse frame))
                                            (dirname path))))))
    (consp
     (assoc-equal
      (basename path)
      (m1-file->contents
       (mv-nth 0
               (hifat-find-file fs (dirname path))))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-mkdir-correctness-lemma-99))
    :use
    (:instance
     (:rewrite abs-mkdir-correctness-lemma-99)
     (fs1
      (m1-file->contents (mv-nth 0
                                 (hifat-find-file (mv-nth 0 (collapse frame))
                                                  (dirname path)))))
     (name (basename path))
     (fs2 (m1-file->contents
           (mv-nth 0
                   (hifat-find-file fs (dirname path)))))))))

(defthm
  abs-mkdir-correctness-lemma-112
  (implies
   (and
    (not (consp path))
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (frame-reps-fs frame fs)
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        frame)))
     (dirname path)))
   (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                  (mv-nth 0 (collapse frame))))
  :hints
  (("goal"
    :in-theory
    (e/d (abs-mkdir collapse)
         ((:DEFINITION ASSOC-EQUAL)
          (:REWRITE ABS-FIND-FILE-CORRECTNESS-2)
          (:REWRITE CONSP-OF-ASSOC-OF-FRAME->FRAME)
          (:REWRITE DEFAULT-CDR)
          (:REWRITE
           ABS-SEPARATE-OF-FRAME->FRAME-OF-COLLAPSE-THIS-LEMMA-8
           . 2)
          (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS)
          (:REWRITE SUBSETP-WHEN-PREFIXP)
          (:REWRITE
           PARTIAL-COLLAPSE-CORRECTNESS-LEMMA-24)))
    :do-not-induct t)))

(defthm
  abs-mkdir-correctness-lemma-116
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (frame-p frame)
        (equal (frame-val->src (cdr (assoc-equal 0 frame)))
               0)
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (frame-reps-fs frame fs)
        (consp (assoc-equal 0 frame))
        (consp (dirname path))
        (not (m1-directory-file-p
              (mv-nth 0
                      (hifat-find-file (mv-nth 0 (collapse frame))
                                       (dirname path))))))
   (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                  (mv-nth 0 (collapse frame))))
  :hints
  (("goal"
    :in-theory
    (e/d (abs-mkdir collapse)
         (abs-file-alist-p-correctness-1 abs-fs-p-correctness-1
                                         abs-fs-p-when-hifat-no-dups-p
                                         abs-mkdir-correctness-lemma-32
                                         abs-separate-correctness-1
                                         collapse-congruence-lemma-4
                                         frame->frame-of-frame-with-root
                                         frame->root-of-frame-with-root
                                         mv-nth-of-cons))
    :do-not-induct t)))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and (absfat-equiv fs1 fs2)
           (abs-fs-p fs1)
           (abs-fs-p fs2)
           (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs1 path))))
      (absfat-equiv
       (abs-file->contents (mv-nth 0 (abs-find-file-helper fs1 path)))
       (abs-file->contents (mv-nth 0
                                   (abs-find-file-helper fs2 path)))))
     :hints (("goal" :in-theory (enable abs-find-file-helper)))))

  (defthm
    abs-mkdir-correctness-lemma-128
    (implies
     (absfat-equiv fs1 fs2)
     (absfat-equiv
      (abs-file->contents (mv-nth 0 (abs-find-file-helper fs1 path)))
      (abs-file->contents (mv-nth 0
                                  (abs-find-file-helper fs2 path)))))
    :hints
    (("goal"
      :in-theory (e/d (abs-file-p-alt absfat-equiv hifat-subsetp
                                      abs-fs-fix m1-regular-file-p)
                      ((:rewrite abs-find-file-helper-of-collapse-lemma-7)))
      :do-not-induct t
      :use ((:instance lemma (fs1 (abs-fs-fix fs1))
                       (fs2 (abs-fs-fix fs2)))
            (:instance lemma (fs1 (abs-fs-fix fs2))
                       (fs2 (abs-fs-fix fs1)))
            (:instance (:rewrite abs-find-file-helper-of-collapse-lemma-7)
                       (path path)
                       (fs fs2))
            (:instance (:rewrite abs-find-file-helper-of-collapse-lemma-7)
                       (path path)
                       (fs fs1)))))
    :rule-classes :congruence))

(defthmd
  abs-mkdir-correctness-lemma-129
  (implies
   (and (zp (abs-find-file-src frame path))
        (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
        (mv-nth 1 (collapse frame))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (abs-separate frame)
        (abs-complete
         (abs-file->contents (mv-nth 0 (abs-find-file frame path))))
        (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (consp (assoc-equal '0 frame)))
   (and
    (equal (abs-find-file-helper (frame-val->dir (cdr (assoc-equal 0 frame)))
                                 path)
           (hifat-find-file (mv-nth 0 (collapse frame))
                            path))
    (equal (abs-find-file-helper (frame->root frame)
                                 path)
           (hifat-find-file (mv-nth 0 (collapse frame))
                            path))))
  :hints
  (("goal"
    :in-theory (e/d (frame->root)
                    (abs-mkdir-correctness-lemma-86))
    :do-not-induct t
    :use
    (:instance
     abs-mkdir-correctness-lemma-86
     (n
      (len
       (frame-val->path (cdr (assoc-equal (abs-find-file-src frame path)
                                          frame)))))))))

(defthm
  abs-mkdir-correctness-lemma-139
  (implies
   (and
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        frame)))
     (dirname path))
    (< 1 (len path)))
   (equal
    (mv-nth
     0
     (abs-place-file-helper
      (frame-val->dir
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path)))))
      (append
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))
        (dirname path))
       (list (basename path)))
      '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
        (contents))))
    (mv-nth
     0
     (abs-place-file-helper
      (frame-val->dir
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path)))))
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))
       path)
      '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
        (contents))))))
  :instructions
  (promote
   (:dive 1 2 2 1 2)
   (:rewrite dirname-alt)
   :top (:dive 1 2 2 2 1)
   (:rewrite basename-alt)
   (:dive 1 1)
   (:rewrite last-alt)
   :top
   (:bash
    ("goal"
     :in-theory (e/d nil)
     :use
     (:instance
      take-of-nthcdr
      (n1
       (-
        (+ -1 (len path))
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))))
      (n2
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame)))))
      (l path))))
   (:dive 1 2 2 1)
   := :top
   (:=
    (list (nth (+ -1 (len path)) path))
    (nthcdr
     (+
      -1 (len path)
      (-
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame))))
      path))
    :hints :none
    :equiv list-equiv)
   (:dive 1 2 2)
   (:claim
    (<=
     (+
      -1 (len path)
      (-
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))))
     (len
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))
       path))))
   (:rewrite binary-append-take-nthcdr)
   :top :bash (:dive 2)
   (:rewrite nthcdr-of-nthcdr)
   :top :bash
   (:= (nthcdr (+ -1 (len path)) path)
       (cons (car (nthcdr (+ -1 (len path)) path))
             (cdr (nthcdr (+ -1 (len path))
                          path)))
       :hints :none)
   (:bash ("goal" :in-theory (disable (:rewrite nthcdr-of-nthcdr))
           :use (:instance (:rewrite nthcdr-of-nthcdr)
                           (x path)
                           (b (+ -1 (len path)))
                           (a 1))))
   (:dive 2)
   (:rewrite cons-car-cdr)
   :top :bash))

(defthm abs-mkdir-correctness-lemma-155
  (implies (and (hifat-equiv y z)
                (syntaxp (not (term-order y z)))
                (equal (hifat-file-alist-fix y) y)
                (equal (hifat-file-alist-fix z) z))
           (equal (m1-directory-file-p (cdr (assoc-equal key y)))
                  (m1-directory-file-p (cdr (assoc-equal key z)))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hifat-equiv)
                           (hifat-subsetp-transitive-lemma-1))
           :use ((:instance hifat-subsetp-transitive-lemma-1
                            (y (hifat-file-alist-fix z))
                            (z (hifat-file-alist-fix y)))
                 (:instance hifat-subsetp-transitive-lemma-1
                            (y (hifat-file-alist-fix y))
                            (z (hifat-file-alist-fix z)))))))

(defthmd
  abs-mkdir-correctness-lemma-157
  (implies
   (and
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        frame)))
     (dirname path))
    (consp path))
   (fat32-filename-list-equiv
    (binary-append
     (nthcdr
      (len
       (frame-val->path$inline
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame))))
      (dirname path))
     (cons (basename path) 'nil))
    (if
     (< 1 (len path))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame))))
      path)
     (list (car path)))))
  :instructions
  (:promote
   (:dive 1 1 2)
   (:rewrite dirname-alt)
   :top (:dive 1 2 1)
   (:rewrite basename-alt)
   (:dive 1 1)
   (:rewrite last-alt)
   :top :bash
   (:bash
    ("goal"
     :in-theory (e/d nil)
     :use
     (:instance
      take-of-nthcdr
      (n1
       (-
        (+ -1 (len path))
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))))
      (n2
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame)))))
      (l path))))
   (:dive 1 1)
   := :top
   (:=
    (list (nth (+ -1 (len path)) path))
    (nthcdr
     (+
      -1 (len path)
      (-
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame))))
      path))
    :hints :none
    :equiv list-equiv)
   (:dive 1)
   (:claim
    (and
     (<=
      (+
       -1 (len path)
       (-
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))))
      (len
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        frame))))
        path)))))
   (:rewrite binary-append-take-nthcdr)
   :top (:change-goal nil t)
   (:dive 2)
   (:rewrite nthcdr-of-nthcdr)
   :top :bash
   (:= (nthcdr (+ -1 (len path)) path)
       (cons (car (nthcdr (+ -1 (len path)) path))
             (cdr (nthcdr (+ -1 (len path))
                          path)))
       :hints :none)
   (:bash ("goal" :in-theory (disable (:rewrite nthcdr-of-nthcdr))
           :use (:instance (:rewrite nthcdr-of-nthcdr)
                           (x path)
                           (b (+ -1 (len path)))
                           (a 1))))
   (:dive 2)
   (:rewrite cons-car-cdr)
   :top
   :bash :bash))

(defthm
  abs-mkdir-correctness-lemma-161
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (equal (frame-val->src (cdr (assoc-equal 0 frame)))
           0)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (frame-reps-fs frame fs)
    (consp (assoc-equal 0 frame))
    (not
     (consp
      (abs-addrs
       (abs-file->contents
        (mv-nth 0
                (abs-find-file (partial-collapse frame (dirname path))
                               (dirname path)))))))
    (equal (mv-nth 1
                   (hifat-find-file (mv-nth 0 (collapse frame))
                                    (dirname path)))
           0))
   (equal
    (mv-nth 1
            (abs-find-file (partial-collapse frame (dirname path))
                           (dirname path)))
    0))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable (:rewrite abs-find-file-correctness-2))
    :use (:instance (:rewrite abs-find-file-correctness-2)
                    (path (dirname path))
                    (frame (partial-collapse frame (dirname path)))))))

(defthm
  hifat-equiv-of-put-assoc-equal-1
  (implies (and (hifat-equiv (m1-file->contents file1)
                             (m1-file->contents file2))
                (syntaxp (not (term-order file1 file2)))
                (m1-directory-file-p (m1-file-fix file1))
                (m1-directory-file-p (m1-file-fix file2)))
           (hifat-equiv (put-assoc-equal name file1 fs)
                        (put-assoc-equal name file2 fs)))
  :hints
  (("goal"
    :induct (mv (put-assoc-equal name file1 fs)
                (put-assoc-equal name file2 fs))
    :in-theory
    (e/d (hifat-no-dups-p hifat-equiv)
         (hifat-subsetp-reflexive-lemma-4
          (:rewrite hifat-file-alist-fix-when-hifat-no-dups-p)
          (:rewrite abs-find-file-helper-when-m1-file-alist-p-lemma-1)
          (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-1)
          (:rewrite abs-file-fix-when-abs-file-p)
          (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-2)
          (:rewrite collapse-hifat-place-file-lemma-10))))
   ("subgoal *1/2"
    :use
    (:instance
     hifat-subsetp-reflexive-lemma-4
     (x
      (list
       (cons (fat32-filename-fix (car (car fs)))
             (m1-file (m1-file->dir-ent file1)
                      (hifat-file-alist-fix (m1-file->contents file1))))))
     (y (hifat-file-alist-fix (cdr fs)))))))

(defthm
  hifat-place-file-when-hifat-equiv-lemma-1
  (implies
   (and
    (hifat-equiv
     (mv-nth
      0
      (hifat-place-file
       (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                            (hifat-file-alist-fix fs))))
       (cdr path)
       file1))
     (mv-nth
      0
      (hifat-place-file
       (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                            (hifat-file-alist-fix fs))))
       (cdr path)
       file2)))
    (syntaxp (not (term-order file1 file2))))
   (hifat-equiv
    (put-assoc-equal
     (fat32-filename-fix (car path))
     (m1-file
      (m1-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car path))
                                          (hifat-file-alist-fix fs))))
      (mv-nth
       0
       (hifat-place-file
        (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                             (hifat-file-alist-fix fs))))
        (cdr path)
        file1)))
     (hifat-file-alist-fix fs))
    (put-assoc-equal
     (fat32-filename-fix (car path))
     (m1-file
      (m1-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car path))
                                          (hifat-file-alist-fix fs))))
      (mv-nth
       0
       (hifat-place-file
        (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                             (hifat-file-alist-fix fs))))
        (cdr path)
        file2)))
     (hifat-file-alist-fix fs))))
  :instructions
  (:promote
   (:dive 1)
   (:rewrite
    hifat-equiv-of-put-assoc-equal-1
    ((file2
      (m1-file
       (m1-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car path))
                                           (hifat-file-alist-fix fs))))
       (mv-nth
        0
        (hifat-place-file
         (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                              (hifat-file-alist-fix fs))))
         (cdr path)
         file2))))))
   :top
   :bash :bash
   :bash :bash))

(defthm
  hifat-place-file-when-hifat-equiv-lemma-2
  (implies (and (hifat-equiv (m1-file->contents file1)
                             (m1-file->contents file2))
                (syntaxp (not (term-order file1 file2)))
                (not (m1-regular-file-p (m1-file-fix file2)))
                (not (m1-regular-file-p (m1-file-fix file1))))
           (hifat-equiv (put-assoc-equal (fat32-filename-fix (car path))
                                         (m1-file-fix file1)
                                         (hifat-file-alist-fix fs))
                        (put-assoc-equal (fat32-filename-fix (car path))
                                         (m1-file-fix file2)
                                         (hifat-file-alist-fix fs))))
  :instructions (:promote (:dive 1)
                          (:rewrite hifat-equiv-of-put-assoc-equal-1
                                    ((file2 (m1-file-fix file2))))
                          :top
                          :bash :bash
                          :bash :bash))

(defthm
  hifat-place-file-when-hifat-equiv-lemma-3
  (implies (and (hifat-equiv (m1-file->contents file1)
                             (m1-file->contents file2))
                (syntaxp (not (term-order file1 file2)))
                (m1-directory-file-p (m1-file-fix file1))
                (m1-directory-file-p (m1-file-fix file2)))
           (hifat-equiv (put-assoc-equal (fat32-filename-fix (car path))
                                         (m1-file-fix file1)
                                         (hifat-file-alist-fix fs))
                        (put-assoc-equal (fat32-filename-fix (car path))
                                         (m1-file-fix file2)
                                         (hifat-file-alist-fix fs))))
  :instructions (:promote (:dive 1)
                          (:rewrite hifat-equiv-of-put-assoc-equal-1
                                    ((file2 (m1-file-fix file2))))
                          :top
                          :bash :bash
                          :bash :bash))

(defthm hifat-place-file-when-hifat-equiv-1
  (implies (and (hifat-equiv (m1-file->contents file1)
                             (m1-file->contents file2))
                (syntaxp (not (term-order file1 file2)))
                (m1-directory-file-p (m1-file-fix file1))
                (m1-directory-file-p (m1-file-fix file2)))
           (hifat-equiv (mv-nth 0 (hifat-place-file fs path file1))
                        (mv-nth 0 (hifat-place-file fs path file2))))
  :hints (("goal" :in-theory (enable hifat-place-file))))

(defthm
  hifat-equiv-of-put-assoc-lemma-1
  (implies (and (m1-file-alist-p fs1)
                (hifat-no-dups-p fs1)
                (hifat-subsetp fs1 fs2)
                (hifat-no-dups-p (m1-file->contents val)))
           (hifat-subsetp (put-assoc-equal key val fs1)
                          (put-assoc-equal key val fs2)))
  :hints (("goal" :in-theory (enable hifat-subsetp)
           :induct (mv (hifat-subsetp fs1 fs2)
                       (put-assoc-equal key val fs1)))))

(defthm hifat-equiv-of-put-assoc-2
  (implies (and (hifat-equiv fs1 fs2)
                (syntaxp (not (term-order fs1 fs2)))
                (m1-file-alist-p fs1)
                (hifat-no-dups-p fs1)
                (m1-file-alist-p fs2)
                (hifat-no-dups-p fs2)
                (m1-file-p val)
                (fat32-filename-p key)
                (hifat-no-dups-p (m1-file->contents val)))
           (hifat-equiv (put-assoc-equal key val fs1)
                        (put-assoc-equal key val fs2)))
  :hints (("goal" :in-theory (enable hifat-equiv)
           :do-not-induct t)))

(encapsulate
  ()

  (local
   (in-theory
    (e/d (abs-mkdir collapse 1st-complete
                    collapse-this hifat-place-file
                    hifat-find-file
                    abs-disassoc
                    abs-mkdir-correctness-lemma-16
                    abs-mkdir-correctness-lemma-3
                    abs-separate dist-names abs-fs-fix
                    abs-addrs frame-addrs-root
                    ctx-app
                    frame->root-of-put-assoc
                    frame->frame-of-put-assoc
                    abs-mkdir-correctness-lemma-88
                    abs-find-file-helper
                    abs-mkdir-correctness-lemma-95
                    abs-place-file-helper)
         ((:rewrite put-assoc-equal-without-change . 2)
          (:rewrite
           abs-separate-of-frame->frame-of-collapse-this-lemma-8
           . 2)
          (:rewrite abs-addrs-of-ctx-app-2)
          (:rewrite remove-when-absent)
          (:rewrite abs-mkdir-correctness-lemma-26)
          (:rewrite
           abs-separate-of-frame->frame-of-collapse-this-lemma-10)
          (:rewrite
           abs-fs-fix-of-put-assoc-equal-lemma-1)
          (:linear count-free-clusters-correctness-1)
          (:rewrite
           partial-collapse-correctness-lemma-24)
          (:rewrite m1-file-p-when-m1-regular-file-p)
          (:definition len)
          (:rewrite abs-directory-file-p-when-m1-file-p)
          (:rewrite
           abs-addrs-when-m1-file-alist-p-lemma-2)
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite abs-file-fix-when-abs-file-p)
          (:rewrite
           ctx-app-ok-when-absfat-equiv-lemma-4)
          (:rewrite abs-find-file-correctness-lemma-2)
          (:linear len-of-seq-this-1)
          (:rewrite assoc-after-remove-assoc)
          (:rewrite abs-mkdir-correctness-lemma-14)
          (:definition acl2-number-listp)
          (:rewrite 1st-complete-correctness-1)
          (:rewrite abs-addrs-when-m1-file-contents-p)
          (:rewrite
           abs-separate-of-frame->frame-of-collapse-this-lemma-11)
          (:rewrite abs-find-file-correctness-1-lemma-3)
          (:rewrite
           absfat-equiv-implies-set-equiv-addrs-at-1-lemma-1)
          (:rewrite
           abs-fs-fix-of-put-assoc-equal-lemma-2)
          (:rewrite final-val-of-collapse-this-lemma-3)
          (:rewrite abs-fs-p-of-ctx-app)
          (:type-prescription
           abs-fs-fix-of-put-assoc-equal-lemma-3)
          (:rewrite m1-file-contents-p-correctness-1)
          (:definition binary-append)
          (:definition true-listp)
          (:rewrite
           partial-collapse-correctness-lemma-2)
          (:definition rational-listp)
          (:rewrite list-equiv-when-true-listp)
          (:rewrite ctx-app-when-not-ctx-app-ok)
          (:rewrite ctx-app-ok-when-abs-complete)
          (:rewrite nth-when->=-n-len-l)
          (:rewrite
           no-duplicatesp-of-abs-addrs-of-remove-assoc-lemma-3)
          (:rewrite
           partial-collapse-correctness-lemma-1)
          (:rewrite
           partial-collapse-correctness-lemma-28)
          (:rewrite
           abs-separate-of-frame->frame-of-collapse-this-lemma-15)
          (:rewrite m1-file-alist-p-when-subsetp-equal)
          (:type-prescription
           abs-find-file-correctness-1-lemma-17)
          abs-mkdir-correctness-lemma-50
          (:rewrite collapse-hifat-place-file-lemma-6)
          (:definition nth)
          (:rewrite
           abs-find-file-after-abs-mkdir-lemma-11)
          (:rewrite
           hifat-find-file-correctness-1-lemma-1)
          abs-separate-of-frame->frame-of-collapse-this-lemma-8
          (:rewrite
           abs-find-file-after-abs-mkdir-lemma-13)
          (:definition strip-cars)
          (:rewrite abs-file-alist-p-correctness-1)
          (:rewrite
           abs-file-alist-p-of-abs-file->contents)
          (:rewrite member-of-abs-addrs-when-natp . 2)
          (:definition hifat-file-alist-fix)
          (:type-prescription assoc-when-zp-len)
          (:rewrite
           abs-place-file-helper-of-ctx-app-lemma-1)
          (:rewrite abs-addrs-of-ctx-app-2)
          (:definition put-assoc-equal)
          (:rewrite abs-mkdir-correctness-lemma-42)
          (:rewrite
           abs-file-contents-fix-when-abs-file-contents-p)
          (:rewrite
           abs-file-contents-p-when-m1-file-contents-p)
          (:rewrite
           hifat-find-file-correctness-1-lemma-1)
          (:rewrite abs-fs-p-of-ctx-app)
          (:definition binary-append)
          (:rewrite absfat-subsetp-transitivity-lemma-7)
          (:rewrite final-val-of-collapse-this-lemma-3)
          (:rewrite assoc-after-remove-assoc)
          (:rewrite abs-find-file-correctness-lemma-2)
          (:rewrite abs-mkdir-correctness-lemma-85)
          (:rewrite abs-mkdir-correctness-lemma-75)
          (:rewrite len-when-prefixp)
          (:rewrite m1-directory-file-p-when-m1-file-p)
          (:rewrite abs-find-file-correctness-lemma-31)
          (:rewrite consp-of-assoc-of-abs-fs-fix)
          (:rewrite
           abs-find-file-correctness-1-lemma-18)
          (:rewrite
           abs-find-file-correctness-1-lemma-40)
          (:rewrite
           abs-separate-of-frame->frame-of-collapse-this-lemma-7)
          (:rewrite nth-when-prefixp)
          (:rewrite
           partial-collapse-correctness-lemma-77)
          (:rewrite abs-addrs-of-ctx-app-1-lemma-2)
          (:rewrite
           collapse-1st-index-correctness-lemma-1)
          (:rewrite member-of-abs-top-addrs)
          (:rewrite abs-mkdir-guard-lemma-3)
          (:rewrite abs-find-file-correctness-lemma-12)
          (:type-prescription
           collapse-hifat-place-file-lemma-1)
          (:linear position-when-member)
          (:linear position-equal-ac-when-member)
          (:rewrite prefixp-one-way-or-another . 1)
          (:rewrite member-of-abs-addrs-when-natp . 1)
          (:rewrite hifat-subsetp-transitive-lemma-1)
          abs-separate-of-frame->frame-of-collapse-this-lemma-13
          (:rewrite append-atom-under-list-equiv)
          (:rewrite abs-mkdir-correctness-lemma-99)
          (:rewrite hifat-subsetp-preserves-assoc-equal)
          (:rewrite
           absfat-equiv-implies-set-equiv-names-at-1-lemma-1)
          (:linear abs-mkdir-correctness-lemma-74)
          (:definition hifat-subsetp)
          (:rewrite member-of-abs-fs-fix-when-natp)
          (:type-prescription
           abs-separate-of-frame->frame-of-collapse-this-lemma-7)
          (:rewrite collapse-hifat-place-file-lemma-1)
          (:rewrite
           partial-collapse-correctness-lemma-106)
          (:rewrite
           m1-file-alist-p-of-cdr-when-m1-file-alist-p)
          (:rewrite abs-mkdir-correctness-lemma-96)
          (:rewrite
           fat32-filename-p-of-nth-when-fat32-filename-list-p)
          (:rewrite m1-file-alist-p-when-not-consp)
          (:rewrite
           abs-fs-fix-of-put-assoc-equal-lemma-3)
          ;; Should this really be disabled?
          (:rewrite abs-mkdir-correctness-lemma-95)
          (:rewrite
           abs-no-dups-p-of-abs-file->contents-of-cdr-of-assoc)
          (:rewrite subsetp-member . 2)
          (:rewrite subsetp-member . 1)
          (:rewrite
           fat32-filename-p-when-member-equal-of-fat32-filename-list-p)
          (:rewrite path-clear-when-prefixp-lemma-1)
          (:rewrite
           absfat-equiv-implies-set-equiv-names-at-1-lemma-2)
          (:rewrite abs-mkdir-correctness-lemma-58)
          (:rewrite subsetp-member . 4)
          (:rewrite ctx-app-ok-when-not-natp)
          (:rewrite ctx-app-when-not-natp)
          (:rewrite collapse-hifat-place-file-lemma-15)
          (:rewrite
           ctx-app-ok-when-absfat-equiv-lemma-3)
          (:rewrite
           abs-find-file-helper-of-collapse-lemma-1)
          (:rewrite
           abs-separate-of-frame->frame-of-collapse-this-lemma-14)
          (:rewrite collapse-hifat-place-file-lemma-9)
          (:rewrite collapse-hifat-place-file-lemma-7)
          (:rewrite collapse-hifat-place-file-lemma-13)
          (:rewrite collapse-hifat-place-file-lemma-11)
          (:rewrite
           absfat-equiv-implies-set-equiv-names-at-1-lemma-4)
          (:rewrite
           abs-find-file-after-abs-mkdir-lemma-7)
          (:rewrite consp-of-remove-assoc-1)
          (:rewrite abs-find-file-correctness-lemma-6)
          (:rewrite
           abs-find-file-of-put-assoc-lemma-7 . 1)
          (:rewrite
           abs-find-file-helper-of-collapse-lemma-2)
          (:rewrite abs-find-file-correctness-lemma-3)
          (:REWRITE
           FAT32-FILENAME-P-OF-CAAR-WHEN-M1-FILE-ALIST-P)
          (:REWRITE SUBSETP-CAR-MEMBER)
          (:REWRITE ABS-MKDIR-CORRECTNESS-LEMMA-59)
          (:REWRITE M1-FILE-ALIST-P-OF-CONS)
          (:REWRITE ABS-MKDIR-CORRECTNESS-LEMMA-102)
          (:LINEAR
           ABS-SEPARATE-OF-FRAME->FRAME-OF-COLLAPSE-THIS-LEMMA-11)
          (:REWRITE ABS-FIND-FILE-CORRECTNESS-LEMMA-14)
          (:REWRITE SUBSETP-TRANS)))))

  (defthm
    abs-mkdir-correctness-lemma-109
    (implies (and (not (consp path)))
             (> (mv-nth 1
                        (hifat-find-file (mv-nth 0 (collapse frame))
                                         path))
                0))
    :rule-classes :type-prescription)

  (defthm
    abs-mkdir-correctness-lemma-110
    (implies
     (and
      (not (consp path)))
     (equal
      (mv-nth 1
              (hifat-place-file
               (mv-nth 0 (collapse frame))
               path
               (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                       t)
                        nil)))
      *enoent*)))

  (defthm
    abs-mkdir-correctness-lemma-111
    (implies
     (and (not (consp path))
          (abs-fs-p fs)
          (m1-file-alist-p fs)
          (frame-reps-fs frame fs))
     (equal
      (mv-nth 0
              (hifat-place-file
               (mv-nth 0 (collapse frame))
               path
               (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                       t)
                        nil)))
      (mv-nth 0 (collapse frame)))))

  (defthm abs-mkdir-correctness-lemma-113
    (implies (not (consp path))
             (equal (mv-nth 2 (abs-mkdir frame path))
                    *enoent*)))

  (defthm
    abs-mkdir-correctness-lemma-114
    (implies
     (and (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (equal (frame-val->src (cdr (assoc-equal 0 frame)))
                 0)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (frame-reps-fs frame fs)
          (consp (assoc-equal 0 frame))
          (not (m1-directory-file-p
                (mv-nth 0
                        (hifat-find-file (mv-nth 0 (collapse frame))
                                         (dirname path))))))
     (equal (mv-nth 2 (abs-mkdir frame path))
            2)))

  (defthm
    abs-mkdir-correctness-lemma-115
    (implies
     (and
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth
           0
           (abs-find-file (partial-collapse frame (dirname path))
                          (dirname path)))))))
      (consp (dirname path))
      (not (equal (mv-nth 1
                          (hifat-find-file (mv-nth 0 (collapse frame))
                                           (dirname path)))
                  0)))
     (equal (mv-nth 2 (abs-mkdir frame path))
            *enoent*)))

  (defthm
    abs-mkdir-correctness-lemma-117
    (implies
     (and
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth
           0
           (abs-find-file (partial-collapse frame (dirname path))
                          (dirname path)))))))
      (consp (dirname path))
      (not (equal (mv-nth 1
                          (hifat-find-file (mv-nth 0 (collapse frame))
                                           (dirname path)))
                  0)))
     (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                    (mv-nth 0 (collapse frame)))))

  (defthm
    abs-mkdir-correctness-lemma-118
    (implies
     (and
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (abs-fs-p fs)
      (m1-file-alist-p fs)
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (remove-assoc-equal
          (basename path)
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr (assoc-equal
                   (abs-find-file-src
                    (partial-collapse frame (dirname path))
                    (dirname path))
                   (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (abs-find-file-src
                      (partial-collapse frame (dirname path))
                      (dirname path))
                     (partial-collapse frame (dirname path))))))
             (dirname path))
            (find-new-index
             (strip-cars
              (partial-collapse frame (dirname path))))))))))
      (not (consp (dirname path)))
      (not (equal (mv-nth 1
                          (hifat-find-file (mv-nth 0 (collapse frame))
                                           path))
                  0)))
     (frame-reps-fs
      (mv-nth 0 (abs-mkdir frame path))
      (mv-nth 0
              (hifat-place-file
               (mv-nth 0 (collapse frame))
               path
               (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                       t)
                        nil)))))
    :hints (("goal" :in-theory (enable frame->root)
             :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-119
    (implies
     (and (fat32-filename-list-equiv (append (dirname path)
                                             (list (basename path)))
                                     path)
          (abs-fs-p fs)
          (m1-file-alist-p fs)
          (frame-reps-fs frame fs)
          (not (consp (dirname path)))
          (equal (mv-nth 1
                         (hifat-find-file (mv-nth 0 (collapse frame))
                                          path))
                 0))
     (equal (mv-nth 2 (abs-mkdir frame path))
            *eexist*))
    :hints (("goal" :in-theory (enable frame->root)
             :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-120
    (implies
     (and
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (not (consp (dirname path)))
      (not (equal (mv-nth 1
                          (hifat-find-file (mv-nth 0 (collapse frame))
                                           path))
                  0)))
     (equal
      (mv-nth 1
              (hifat-place-file
               (mv-nth 0 (collapse frame))
               path
               (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                       t)
                        nil)))
      0)))

  (defthm
    abs-mkdir-correctness-lemma-121
    (implies
     (and (fat32-filename-list-equiv (append (dirname path)
                                             (list (basename path)))
                                     path)
          (frame-reps-fs frame fs)
          (not (consp (dirname path)))
          (not (equal (mv-nth 1
                              (hifat-find-file (mv-nth 0 (collapse frame))
                                               path))
                      0)))
     (equal (mv-nth 2 (abs-mkdir frame path))
            0)))

  (defthm
    abs-mkdir-correctness-lemma-124
    (implies
     (and
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (mv-nth 1 (collapse frame))
      (hifat-equiv (mv-nth 0 (collapse frame))
                   fs)
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth
           0
           (abs-find-file (partial-collapse frame (dirname path))
                          (dirname path)))))))
      (list-equiv
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame)))
       (dirname path)))
     (> (mv-nth 1
                (hifat-find-file fs (dirname path)))
        0))
    :hints
    (("goal"
      :in-theory (disable abs-find-file-src-correctness-2
                          hifat-equiv-implies-equal-mv-nth-1-hifat-find-file-2)
      :use
      ((:instance abs-find-file-src-correctness-2
                  (frame (partial-collapse frame (dirname path)))
                  (path (dirname path)))
       (:instance
        hifat-equiv-implies-equal-mv-nth-1-hifat-find-file-2
        (m1-file-alist1
         (mv-nth 0
                 (collapse (partial-collapse frame (dirname path)))))
        (m1-file-alist2 fs)
        (path (dirname path))))))
    :rule-classes :linear)

  (defthm
    abs-mkdir-correctness-lemma-125
    (implies
     (and
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (abs-fs-p fs)
      (m1-file-alist-p fs)
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth
           0
           (abs-find-file (partial-collapse frame (dirname path))
                          (dirname path)))))))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame)))
       (dirname path))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      path))
             0))
     (equal (mv-nth 2 (abs-mkdir frame path))
            *eexist*))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-132
    (implies
     (and
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (equal
       (len
        (frame-val->path
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path))))))
       0)
      (abs-fs-p fs)
      (m1-file-alist-p fs)
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (remove-assoc-equal
          (basename path)
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal (abs-find-file-src
                            (partial-collapse frame (dirname path))
                            (dirname path))
                           (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (abs-find-file-src
                      (partial-collapse frame (dirname path))
                      (dirname path))
                     (partial-collapse frame (dirname path))))))
             (dirname path))
            (find-new-index
             (strip-cars
              (partial-collapse frame (dirname path))))))))))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth
           0
           (abs-find-file (partial-collapse frame (dirname path))
                          (dirname path)))))))
      (not
       (member-equal
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path))))
        (abs-addrs
         (frame-val->dir
          (cdr
           (assoc-equal
            (abs-find-file-src (partial-collapse frame (dirname path))
                               (dirname path))
            (partial-collapse frame (dirname path))))))))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame)))
       (dirname path))
      (not
       (equal
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (dirname path)
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))))
      (consp (dirname path))
      (not (m1-directory-file-p
            (mv-nth 0
                    (hifat-find-file (mv-nth 0 (collapse frame))
                                     (dirname path))))))
     (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                    (mv-nth 0 (collapse frame))))
    :hints (("Goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-134
    (implies
     (and
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root (partial-collapse frame (dirname path)))
         (put-assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src
                   (partial-collapse frame (dirname path))
                   (dirname path))
                  (frame->frame
                   (partial-collapse frame (dirname path))))))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir
              (cdr
               (assoc-equal
                (abs-find-file-src
                 (partial-collapse frame (dirname path))
                 (dirname path))
                (frame->frame
                 (partial-collapse frame (dirname path))))))
             (append
              (nthcdr
               (len
                (frame-val->path
                 (cdr
                  (assoc-equal
                   (abs-find-file-src
                    (partial-collapse frame (dirname path))
                    (dirname path))
                   frame))))
               (dirname path))
              (list (basename path)))
             '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
               (contents))))
           (frame-val->src
            (cdr
             (assoc-equal
              (abs-find-file-src
               (partial-collapse frame (dirname path))
               (dirname path))
              (frame->frame
               (partial-collapse frame (dirname path)))))))
          (frame->frame (partial-collapse frame (dirname path)))))))
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (not
       (equal
        0
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path)))))
     (mv-nth
      1
      (collapse
       (frame-with-root
        (frame->root (partial-collapse frame (dirname path)))
        (put-assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (frame-val
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src
                  (partial-collapse frame (dirname path))
                  (dirname path))
                 frame)))
          (mv-nth
           0
           (abs-place-file-helper
            (frame-val->dir
             (cdr (assoc-equal
                   (abs-find-file-src
                    (partial-collapse frame (dirname path))
                    (dirname path))
                   (partial-collapse frame (dirname path)))))
            (append
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (abs-find-file-src
                   (partial-collapse frame (dirname path))
                   (dirname path))
                  frame))))
              (dirname path))
             (list (basename path)))
            '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (contents))))
          (frame-val->src
           (cdr (assoc-equal
                 (abs-find-file-src
                  (partial-collapse frame (dirname path))
                  (dirname path))
                 frame))))
         (frame->frame
          (partial-collapse frame (dirname path))))))))
    :hints
    (("goal" :in-theory (e/d (frame->root abs-mkdir-correctness-lemma-13)
                             ((:rewrite abs-find-file-after-abs-mkdir-lemma-5)))
      :use (:instance (:rewrite abs-find-file-after-abs-mkdir-lemma-5)
                      (path (dirname path))
                      (frame frame)))))

  (defthm
    abs-mkdir-correctness-lemma-136
    (implies
     (frame-p frame)
     (frame-p (partial-collapse frame (dirname path))))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-140
    (abs-fs-p
     (ctx-app
      (mv-nth
       1
       (abs-disassoc
        (frame-val->dir
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       (partial-collapse frame (dirname path)))))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src
                  (partial-collapse frame (dirname path))
                  (dirname path))
                 frame))))
         (dirname path))
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path))))))
      (mv-nth
       0
       (abs-disassoc
        (frame-val->dir
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       (partial-collapse frame (dirname path)))))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src
                  (partial-collapse frame (dirname path))
                  (dirname path))
                 frame))))
         (dirname path))
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path))))))
      (find-new-index
       (strip-cars (partial-collapse frame (dirname path))))
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))
       (dirname path)))))

  (defthm
    abs-mkdir-correctness-lemma-141
    (implies
     (and
      (frame-p frame))
     (frame-p
      (frame->frame
       (frame-with-root
        (frame->root (partial-collapse frame (dirname path)))
        (frame->frame (partial-collapse frame (dirname path))))))))

  (defthm
    abs-mkdir-correctness-lemma-142
    (abs-fs-p
     (mv-nth
      0
      (abs-place-file-helper
       (mv-nth
        0
        (abs-disassoc
         (frame-val->dir
          (cdr
           (assoc-equal (abs-find-file-src
                         (partial-collapse frame (dirname path))
                         (dirname path))
                        (partial-collapse frame (dirname path)))))
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src
                   (partial-collapse frame (dirname path))
                   (dirname path))
                  frame))))
          (dirname path))
         (find-new-index
          (strip-cars (partial-collapse frame (dirname path))))))
       (list (basename path))
       '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
         (contents))))))

  (defthm
    abs-mkdir-correctness-lemma-143
    (implies
     (and
      (equal
       (mv-nth 1
               (abs-find-file (partial-collapse frame (dirname path))
                              (dirname path)))
       2)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth
           0
           (abs-find-file (partial-collapse frame (dirname path))
                          (dirname path))))))))
     (> (mv-nth 1
                (hifat-find-file (mv-nth 0 (collapse frame))
                                 (dirname path)))
        0))
    :hints (("goal" :do-not-induct t))
    :rule-classes :linear)

  (defthm
    abs-mkdir-correctness-lemma-144
    (implies
     (and
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame)))
       (dirname path)))
     (prefixp
      (frame-val->path
       (cdr
        (assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (partial-collapse frame (dirname path)))))
      (fat32-filename-list-fix (dirname path))))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-145
    (implies
     (and
      (consp (assoc-equal 0 frame)))
     (consp
      (assoc-equal
       (abs-find-file-src (partial-collapse frame (dirname path))
                          (dirname path))
       (partial-collapse frame (dirname path)))))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-146
    (implies
     (and
      (no-duplicatesp-equal (strip-cars frame)))
     (no-duplicatesp-equal
      (strip-cars
       (frame->frame
        (frame-with-root
         (frame->root (partial-collapse frame (dirname path)))
         (frame->frame (partial-collapse frame (dirname path))))))))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-147
    (implies
     (and
      (no-duplicatesp-equal (strip-cars frame)))
     (no-duplicatesp-equal
      (strip-cars (partial-collapse frame (dirname path)))))
    :hints (("goal" :do-not-induct t)))


  (defthm
    abs-mkdir-correctness-lemma-148
    (implies
     (and
      (not (equal (mv-nth 2 (abs-mkdir frame path))
                  0))
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (abs-fs-p fs)
      (m1-file-alist-p fs)
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth
           0
           (abs-find-file (partial-collapse frame (dirname path))
                          (dirname path)))))))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame)))
       (dirname path))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path)))))
     (equal (mv-nth 1
                    (hifat-find-file (mv-nth 0 (collapse frame))
                                     path))
            0))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-149
    (implies
     (and
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth
           0
           (abs-find-file (partial-collapse frame (dirname path))
                          (dirname path)))))))
      (not
       (member-equal
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path))))
        (abs-addrs
         (frame-val->dir
          (cdr
           (assoc-equal
            (abs-find-file-src (partial-collapse frame (dirname path))
                               (dirname path))
            (partial-collapse frame (dirname path))))))))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame)))
       (dirname path))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      path))
             0))
     (ctx-app-ok
      (mv-nth
       1
       (abs-disassoc
        (frame-val->dir
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       (partial-collapse frame (dirname path)))))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src
                  (partial-collapse frame (dirname path))
                  (dirname path))
                 frame))))
         (dirname path))
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path))))))
      (find-new-index
       (strip-cars (partial-collapse frame (dirname path))))
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))
       (dirname path))))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-150
    (implies
     (and
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (frame-reps-fs frame fs))
     (dist-names
      (frame->root
       (frame-with-root
        (frame->root (partial-collapse frame (dirname path)))
        (frame->frame (partial-collapse frame (dirname path)))))
      nil
      (frame->frame
       (frame-with-root
        (frame->root (partial-collapse frame (dirname path)))
        (frame->frame (partial-collapse frame (dirname path)))))))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-151
    (implies
     (and
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth
           0
           (abs-find-file (partial-collapse frame (dirname path))
                          (dirname path)))))))
      (not
       (member-equal
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path))))
        (abs-addrs
         (frame-val->dir
          (cdr
           (assoc-equal
            (abs-find-file-src (partial-collapse frame (dirname path))
                               (dirname path))
            (partial-collapse frame (dirname path))))))))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          frame)))
       (dirname path))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path)))))
     (ctx-app-ok
      (mv-nth
       1
       (abs-disassoc
        (frame-val->dir
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       (partial-collapse frame (dirname path)))))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src
                  (partial-collapse frame (dirname path))
                  (dirname path))
                 frame))))
         (dirname path))
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path))))))
      (find-new-index
       (strip-cars (partial-collapse frame (dirname path))))
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (abs-find-file-src
                        (partial-collapse frame (dirname path))
                        (dirname path))
                       frame))))
       (dirname path))))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-152
    (implies
     (and
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
      (not (equal (mv-nth 1
                          (hifat-find-file (mv-nth 0 (collapse frame))
                                           path))
                  0)))
     (equal
      (mv-nth 1
              (hifat-place-file
               (mv-nth 0 (collapse frame))
               path
               (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                       t)
                        nil)))
      0))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-153
    (implies
     (and
      (not
       (member-equal
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path))))
        (abs-addrs
         (frame-val->dir
          (cdr
           (assoc-equal
            (abs-find-file-src (partial-collapse frame (dirname path))
                               (dirname path))
            (partial-collapse frame (dirname path)))))))))
     (not
      (member-equal
       (fat32-filename-fix (car (list (basename path))))
       (names-at
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr
            (assoc-equal (abs-find-file-src
                          (partial-collapse frame (dirname path))
                          (dirname path))
                         (partial-collapse frame (dirname path)))))
          (nthcdr
           (len
            (frame-val->path
             (cdr (assoc-equal
                   (abs-find-file-src
                    (partial-collapse frame (dirname path))
                    (dirname path))
                   frame))))
           (dirname path))
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (nthcdr
         (len
          (frame-val->path
           (cdr
            (assoc-equal (abs-find-file-src
                          (partial-collapse frame (dirname path))
                          (dirname path))
                         frame))))
         (dirname path))))))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-154
    (implies
     (and
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (abs-fs-p fs)
      (m1-file-alist-p fs)
      (frame-reps-fs frame fs)
      (not (consp (dirname path)))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      path))
             0))
     (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                    (mv-nth 0 (collapse frame))))
    :hints (("goal" :do-not-induct t
             :in-theory (enable frame->root))))

  (defthm
    abs-mkdir-correctness-lemma-156
    (implies
     (and
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (frame-reps-fs frame fs))
     (abs-separate
      (frame->frame
       (frame-with-root
        (frame->root (partial-collapse frame (dirname path)))
        (frame->frame (partial-collapse frame (dirname path)))))))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-159
    (implies
     (not (equal (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 0))
     (consp
      (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   (frame->frame (partial-collapse frame (dirname path))))))
    :hints (("goal" :do-not-induct t))
    :rule-classes :type-prescription)

  (defthm
    abs-mkdir-correctness-lemma-162
    (implies
     (and
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root (partial-collapse frame (dirname path)))
         (put-assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (frame->frame frame))))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir
              (cdr
               (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                (frame->frame (partial-collapse frame (dirname path))))))
             (append
              (nthcdr
               (len
                (frame-val->path
                 (cdr
                  (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame))))
               (dirname path))
              (list (basename path)))
             '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
               (contents))))
           (frame-val->src
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (frame->frame frame)))))
          (frame->frame (partial-collapse frame (dirname path)))))))
      (not (equal 0
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path)))))
     (mv-nth
      1
      (collapse
       (frame-with-root
        (frame->root (partial-collapse frame (dirname path)))
        (put-assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (frame-val
          (frame-val->path
           (cdr
            (assoc-equal
             (abs-find-file-src (partial-collapse frame (dirname path))
                                (dirname path))
             frame)))
          (mv-nth
           0
           (abs-place-file-helper
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (append
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  frame))))
              (dirname path))
             (list (basename path)))
            '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (contents))))
          (frame-val->src
           (cdr
            (assoc-equal
             (abs-find-file-src (partial-collapse frame (dirname path))
                                (dirname path))
             frame))))
         (remove-assoc-equal
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))
          (frame->frame (partial-collapse frame (dirname path)))))))))
    :hints (("goal" :do-not-induct t
             :in-theory (enable abs-mkdir-correctness-lemma-13))))

  (defthm
    abs-mkdir-correctness-lemma-163
    (implies
     (and
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (m1-file-alist-p fs)
      (mv-nth 1 (collapse frame))
      (hifat-equiv (mv-nth 0 (collapse frame))
                   fs)
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))))
      (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path))))
      (consp
       (assoc-equal
        (basename path)
        (m1-file->contents (mv-nth 0
                                   (hifat-find-file fs (dirname path))))))
      (equal 0
             (abs-find-file-src (partial-collapse frame (dirname path))
                                (dirname path))))
     (consp
      (assoc-equal
       (basename path)
       (abs-file->contents
        (mv-nth
         0
         (abs-find-file-helper
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (dirname path)))))))
    :hints
    (("goal" :in-theory (disable abs-find-file-src-correctness-2)
      :use (:instance abs-find-file-src-correctness-2
                      (frame (partial-collapse frame (dirname path)))
                      (path (dirname path)))
      :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-164
    (implies
     (and
      (equal
       (ctx-app
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (partial-collapse frame (dirname path)))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path))
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (mv-nth
         0
         (abs-place-file-helper
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (list (basename path))
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))))
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
         (dirname path)))
       (mv-nth
        0
        (abs-place-file-helper
         (ctx-app
          (mv-nth
           1
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (find-new-index (strip-cars (partial-collapse frame (dirname path))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path)))
         (append
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path))
          (list (basename path)))
         '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (abs-fs-p fs)
      (m1-file-alist-p fs)
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      frame)))
       (dirname path))
      (not
       (equal
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (dirname path)
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      path))
             0))
     (equal (mv-nth 0 (abs-mkdir frame path))
            (partial-collapse frame (dirname path))))
    :hints
    (("goal" :do-not-induct t
      :in-theory (e/d nil
                      ((:definition collapse)
                       (:definition collapse-this)
                       (:definition ctx-app)
                       (:definition 1st-complete)
                       (:definition remove-assoc-equal)
                       (:rewrite collapse-congruence-lemma-4)
                       (:rewrite abs-mkdir-correctness-lemma-100 . 2)
                       (:rewrite prefixp-when-equal-lengths)
                       (:rewrite abs-place-file-helper-correctness-2)
                       (:rewrite abs-mkdir-correctness-lemma-73)
                       (:definition frame-addrs-root)
                       (:linear abs-mkdir-correctness-lemma-124)
                       (:rewrite abs-mkdir-correctness-lemma-16 . 2)
                       (:rewrite abs-find-file-helper-of-collapse-2 . 2)
                       (:rewrite abs-find-file-helper-of-collapse-1 . 2)
                       (:rewrite abs-disassoc-correctness-1)
                       (:definition dist-names)
                       (:rewrite abs-mkdir-correctness-lemma-27))))))

  (defthm
    abs-mkdir-correctness-lemma-165
    (implies
     (and
      (equal
       (ctx-app
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (partial-collapse frame (dirname path)))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path))
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (mv-nth
         0
         (abs-place-file-helper
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (list (basename path))
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))))
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
         (dirname path)))
       (mv-nth
        0
        (abs-place-file-helper
         (ctx-app
          (mv-nth
           1
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (find-new-index (strip-cars (partial-collapse frame (dirname path))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path)))
         (append
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path))
          (list (basename path)))
         '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (abs-fs-p fs)
      (m1-file-alist-p fs)
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      frame)))
       (dirname path))
      (not
       (equal
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (dirname path)
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      path))
             0))
     (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                    (mv-nth 0 (collapse frame))))
    :hints
    (("goal" :do-not-induct t
      :in-theory (e/d ()
                      (abs-mkdir
                       (:rewrite abs-mkdir-correctness-lemma-43)
                       (:rewrite abs-mkdir-correctness-lemma-125)
                       (:rewrite abs-mkdir-correctness-lemma-148)
                       (:definition remove-assoc-equal)
                       (:definition assoc-equal)
                       (:definition 1st-complete)
                       (:rewrite abs-mkdir-correctness-lemma-122)
                       (:rewrite remove-assoc-when-absent-1)
                       (:definition collapse-this)
                       (:definition collapse))))))

  (defthm
    abs-mkdir-correctness-lemma-166
    (equal
     (remove-assoc-equal
      (find-new-index (strip-cars (partial-collapse frame (dirname path))))
      (frame->frame (partial-collapse frame (dirname path))))
     (frame->frame (partial-collapse frame (dirname path))))
    :hints (("goal" :in-theory (enable abs-mkdir-correctness-lemma-13)
             :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-167
    (implies
     (and (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (mv-nth 1 (collapse frame))
          (abs-separate frame))
     (mv-nth
      1
      (collapse
       (frame-with-root
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
        (frame->frame (partial-collapse frame (dirname path)))))))
    :instructions
    (:promote
     (:= (frame-val->dir
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path)))))
         (frame->root (partial-collapse frame (dirname path)))
         :hints (("goal" :in-theory (enable frame->root))))
     :bash))

  (defthm
    abs-mkdir-correctness-lemma-168
    (implies
     (and
      (equal
       (ctx-app
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (dirname path)
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (put-assoc-equal
         (basename path)
         '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents))
         (mv-nth
          0
          (abs-disassoc
           (frame-val->dir
            (cdr (assoc-equal 0
                              (partial-collapse frame (dirname path)))))
           (dirname path)
           (find-new-index
            (strip-cars (partial-collapse frame (dirname path)))))))
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (dirname path))
       (mv-nth
        0
        (abs-place-file-helper
         (frame-val->dir
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path)))))
         path
         '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (mv-nth 1 (collapse frame))
      (abs-separate frame)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (remove-assoc-equal
          (basename path)
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr (assoc-equal 0
                               (partial-collapse frame (dirname path)))))
            (dirname path)
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))))))
      (not
       (equal
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (dirname path)
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))))
      (path-clear (dirname path)
                  (frame->frame (partial-collapse frame (dirname path)))))
     (mv-nth
      1
      (collapse
       (frame-with-root
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (dirname path)
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (cons
         (cons
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))
          (frame-val
           (dirname path)
           (put-assoc-equal
            (basename path)
            '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (contents))
            (mv-nth
             0
             (abs-disassoc
              (frame-val->dir
               (cdr (assoc-equal 0
                                 (partial-collapse frame (dirname path)))))
              (dirname path)
              (find-new-index
               (strip-cars (partial-collapse frame (dirname path)))))))
           0))
         (frame->frame (partial-collapse frame (dirname path))))))))
    :hints
    (("goal"
      :expand
      (collapse
       (frame-with-root
        (mv-nth
         '1
         (abs-disassoc
          (frame-val->dir$inline
           (cdr (assoc-equal '0
                             (partial-collapse frame (dirname path)))))
          (dirname path)
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (cons
         (cons
          (find-new-index (strip-cars (partial-collapse frame (dirname path))))
          (frame-val
           (dirname path)
           (put-assoc-equal
            (basename path)
            '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (contents))
            (mv-nth
             '0
             (abs-disassoc
              (frame-val->dir$inline
               (cdr (assoc-equal '0
                                 (partial-collapse frame (dirname path)))))
              (dirname path)
              (find-new-index
               (strip-cars (partial-collapse frame (dirname path)))))))
           '0))
         (frame->frame (partial-collapse frame (dirname path)))))))))

  (defthm
    abs-mkdir-correctness-lemma-169
    (implies
     (and (hifat-equiv (mv-nth 0 (collapse frame))
                       fs)
          (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path)))))
     (m1-directory-file-p (mv-nth '0
                                  (hifat-find-file (mv-nth '0 (collapse frame))
                                                   (dirname path)))))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-170
   (abs-no-dups-p
    (remove1-assoc-equal
     (basename path)
     (mv-nth
      0
      (abs-disassoc
       (frame-val->dir$inline
        (cdr (assoc-equal 0
                          (partial-collapse frame (dirname path)))))
       (dirname path)
       (find-new-index
        (strip-cars (partial-collapse frame (dirname path)))))))))

  (defthm
    abs-mkdir-correctness-lemma-171
    (implies
     (and (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (mv-nth 1 (collapse frame))
          (abs-separate frame))
     (absfat-equiv
      (mv-nth
       0
       (collapse
        (frame-with-root
         (frame-val->dir
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path)))))
         (frame->frame (partial-collapse frame (dirname path))))))
      (mv-nth 0 (collapse frame))))
    :instructions
    (:promote
     (:= (frame-val->dir
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path)))))
         (frame->root (partial-collapse frame (dirname path)))
         :hints (("goal" :in-theory (enable frame->root))))
     :bash))

  (defthm
    abs-mkdir-correctness-lemma-172
    (implies
     (and
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (m1-file-alist-p fs)
      (mv-nth 1 (collapse frame))
      (hifat-equiv (mv-nth 0 (collapse frame))
                   fs)
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path))))
      (not
       (consp
        (assoc-equal
         (basename path)
         (m1-file->contents (mv-nth 0
                                    (hifat-find-file fs (dirname path)))))))
      (consp path))
     (absfat-equiv
      (mv-nth
       0
       (abs-place-file-helper
        (mv-nth
         0
         (collapse
          (frame-with-root
           (frame-val->dir
            (cdr (assoc-equal 0
                              (partial-collapse frame (dirname path)))))
           (frame->frame (partial-collapse frame (dirname path))))))
        path
        '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          (contents))))
      (mv-nth
       0
       (hifat-place-file
        (mv-nth 0 (collapse frame))
        (dirname path)
        (m1-file
         (m1-file->dir-ent (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
         (put-assoc-equal
          (basename path)
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))
          (m1-file->contents
           (mv-nth 0
                   (hifat-find-file (mv-nth 0 (collapse frame))
                                    (dirname path))))))))))
    :instructions (:promote (:dive 1)
                            (:rewrite abs-mkdir-correctness-lemma-60
                                      ((fs2 (mv-nth 0 (collapse frame)))))
                            :top (:change-goal nil t)
                            :bash :bash
                            :bash :bash))

  (defthm
    abs-mkdir-correctness-lemma-173
    (implies
     (and
      (not
       (consp
        (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                        (dirname path))
                     (frame->frame (partial-collapse frame (dirname path))))))
      (equal
       (ctx-app
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (partial-collapse frame (dirname path)))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path))
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (mv-nth
         0
         (abs-place-file-helper
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (list (basename path))
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))))
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
         (dirname path)))
       (mv-nth
        0
        (abs-place-file-helper
         (ctx-app
          (mv-nth
           1
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (find-new-index (strip-cars (partial-collapse frame (dirname path))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path)))
         (append
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path))
          (list (basename path)))
         '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (abs-fs-p fs)
      (m1-file-alist-p fs)
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (remove-assoc-equal
          (basename path)
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (partial-collapse frame (dirname path))))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))))))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))))
      (not
       (member-equal
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (abs-addrs
         (frame-val->dir
          (cdr (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                (partial-collapse frame (dirname path))))))))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      frame)))
       (dirname path))
      (not
       (equal
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (dirname path)
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))))
      (path-clear (dirname path)
                  (frame->frame (partial-collapse frame (dirname path))))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
      (not (equal (mv-nth 1
                          (hifat-find-file (mv-nth 0 (collapse frame))
                                           path))
                  0)))
     (frame-reps-fs
      (mv-nth 0 (abs-mkdir frame path))
      (mv-nth 0
              (hifat-place-file
               (mv-nth 0 (collapse frame))
               path
               (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                       t)
                        nil)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d nil
                      ((:rewrite abs-mkdir-correctness-lemma-164)
                       (:rewrite abs-mkdir-correctness-lemma-148)
                       (:rewrite abs-mkdir-correctness-lemma-125)
                       (:rewrite abs-find-file-correctness-1-lemma-3)
                       (:rewrite abs-addrs-when-m1-file-alist-p)
                       (:rewrite subsetp-when-prefixp)
                       (:rewrite partial-collapse-correctness-lemma-24)
                       (:rewrite abs-mkdir-correctness-lemma-43)
                       (:rewrite collapse-congruence-lemma-4)
                       (:linear abs-mkdir-correctness-lemma-143)
                       (:rewrite names-at-of-abs-place-file-helper-1)
                       (:type-prescription 1st-complete-correctness-1)
                       (:rewrite consp-of-assoc-of-frame->frame)
                       (:rewrite abs-disassoc-correctness-1)
                       (:rewrite abs-mkdir-correctness-lemma-155)
                       (:rewrite hifat-find-file-correctness-lemma-2)
                       (:rewrite abs-place-file-helper-correctness-1)
                       (:rewrite abs-find-file-after-abs-mkdir-lemma-14)
                       (:rewrite abs-place-file-helper-correctness-2)
                       (:rewrite abs-find-file-helper-of-collapse-1 . 2)
                       (:rewrite abs-find-file-helper-of-collapse-2 . 2)
                       (:rewrite integer-listp-when-not-consp)
                       (:rewrite hifat-find-file-correctness-lemma-4))))))

  (defthm
    abs-mkdir-correctness-lemma-174
    (implies
     (and
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root (partial-collapse frame (dirname path)))
         (put-assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (frame->frame frame))))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir
              (cdr
               (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                (frame->frame (partial-collapse frame (dirname path))))))
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  frame))))
              path)
             '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
               (contents))))
           (frame-val->src
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (frame->frame frame)))))
          (frame->frame (partial-collapse frame (dirname path)))))))
      (not (equal 0
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path)))))
     (mv-nth
      1
      (collapse
       (frame-with-root
        (frame->root (partial-collapse frame (dirname path)))
        (put-assoc-equal
         (abs-find-file-src (partial-collapse frame (dirname path))
                            (dirname path))
         (frame-val
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame)))
          (mv-nth
           0
           (abs-place-file-helper
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             path)
            '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                       0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
              (contents))))
          (frame-val->src
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
         (frame->frame (partial-collapse frame (dirname path))))))))
    :hints (("goal" :in-theory (enable abs-mkdir-correctness-lemma-13))))

  (defthm
    abs-mkdir-correctness-lemma-175
    (implies (and (not (consp (cdr path))))
             (not (consp (dirname path))))
    :hints (("goal" :in-theory (enable dirname-alt len hifat-find-file)))
    :rule-classes :type-prescription)

  (defthm
    abs-mkdir-correctness-lemma-180
    (implies
     (and
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (not
       (equal
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (dirname path)
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path))))))))
     (ctx-app-ok
      (mv-nth
       1
       (abs-disassoc
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
        (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                (dirname path))
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path))))))
      (find-new-index (strip-cars (partial-collapse frame (dirname path))))
      (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
              (dirname path))))
    :hints
    (("goal" :do-not-induct t
      :in-theory
      (e/d (abs-mkdir-correctness-lemma-157)
           ((:rewrite abs-mkdir-correctness-lemma-148)
            (:rewrite collapse-congruence-lemma-4)
            (:linear abs-mkdir-correctness-lemma-143)
            (:rewrite abs-mkdir-correctness-lemma-100 . 2)
            (:rewrite abs-find-file-after-abs-mkdir-lemma-14)
            (:rewrite abs-mkdir-correctness-lemma-155)
            (:rewrite absfat-place-file-correctness-lemma-6)
            (:rewrite hifat-find-file-correctness-lemma-2)
            (:rewrite hifat-find-file-correctness-lemma-4)
            (:rewrite 1st-complete-of-put-assoc-lemma-1)
            (:rewrite absfat-equiv-implies-set-equiv-addrs-at-1-lemma-2)
            (:rewrite abs-mkdir-correctness-lemma-39)
            (:rewrite fat32-filename-list-p-when-subsetp-equal)
            (:definition no-duplicatesp-equal)))))
    :otf-flg t)

  (defthm
    abs-mkdir-correctness-lemma-181
    (implies
     (not
      (member-equal
       (find-new-index (strip-cars (partial-collapse frame (dirname path))))
       (abs-addrs
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path))))))))
     (not
      (member-equal
       (fat32-filename-fix (car (list (basename path))))
       (names-at
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                  (dirname path))
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                (dirname path))))))
    :hints (("goal" :do-not-induct t)))

  (defthm
    abs-mkdir-correctness-lemma-182
    (implies
     (not (equal (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 0))
     (equal
      (mv-nth
       0
       (collapse
        (frame-with-root
         (frame->root (partial-collapse frame (dirname path)))
         (put-assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (frame->frame frame))))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir
              (cdr
               (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                (frame->frame (partial-collapse frame (dirname path))))))
             (append
              (nthcdr
               (len
                (frame-val->path
                 (cdr
                  (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame))))
               (dirname path))
              (list (basename path)))
             '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
               (contents))))
           (frame-val->src
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  (frame->frame frame)))))
          (frame->frame (partial-collapse frame (dirname path)))))))
      (mv-nth
       0
       (collapse
        (frame-with-root
         (frame->root (partial-collapse frame (dirname path)))
         (put-assoc-equal
          (abs-find-file-src (partial-collapse frame (dirname path))
                             (dirname path))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  frame)))
           (mv-nth
            0
            (abs-place-file-helper
             (frame-val->dir
              (cdr
               (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                (partial-collapse frame (dirname path)))))
             (append
              (nthcdr
               (len
                (frame-val->path
                 (cdr
                  (assoc-equal
                   (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame))))
               (dirname path))
              (list (basename path)))
             '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                        0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
               (contents))))
           (frame-val->src
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  frame))))
          (frame->frame (partial-collapse frame (dirname path)))))))))
    :hints (("goal" :in-theory (enable abs-mkdir-correctness-lemma-13))))

  (defthm
    abs-mkdir-correctness-lemma-183
    (implies
     (and (hifat-no-dups-p (m1-file->contents file))
          (no-duplicatesp-equal (strip-cars frame))
          (frame-p frame)
          (equal (frame-val->src (cdr (assoc-equal 0 frame)))
                 0)
          (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
          (mv-nth 1 (collapse frame))
          (abs-separate frame)
          (subsetp-equal (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame))))
     (absfat-equiv
      (mv-nth 0
              (hifat-place-file
               (mv-nth 0
                       (collapse (partial-collapse frame (dirname path))))
               path2 file))
      (mv-nth 0
              (hifat-place-file (mv-nth 0 (collapse frame))
                                path2 file))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable (:rewrite hifat-place-file-correctness-4))
      :use
      (:instance
       (:rewrite hifat-place-file-correctness-4)
       (file file)
       (path path2)
       (m1-file-alist2
        (mv-nth 0
                (collapse (partial-collapse frame (dirname path)))))
       (m1-file-alist1 (mv-nth 0 (collapse frame)))))))

  (defthm
    abs-mkdir-correctness-lemma-184
    (implies
     (and
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (m1-file-alist-p fs)
      (mv-nth 1 (collapse frame))
      (hifat-equiv (mv-nth 0 (collapse frame))
                   fs)
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      frame)))
       (dirname path))
      (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path))))
      (not
       (consp
        (assoc-equal
         (basename path)
         (m1-file->contents (mv-nth 0
                                    (hifat-find-file fs (dirname path)))))))
      (consp path))
     (absfat-equiv
      (mv-nth
       0
       (hifat-place-file
        (mv-nth 0 (collapse frame))
        (append
         (frame-val->path
          (cdr (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                (frame->frame frame))))
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  frame))))
          (dirname path))
         (list (basename path)))
        '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          (contents))))
      (mv-nth
       0
       (hifat-place-file
        (mv-nth 0 (collapse frame))
        (dirname path)
        (m1-file
         (m1-file->dir-ent (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
         (put-assoc-equal
          (basename path)
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))
          (m1-file->contents
           (mv-nth 0
                   (hifat-find-file (mv-nth 0 (collapse frame))
                                    (dirname path))))))))))
    :instructions
    (:promote
     (:dive 1 2 2 1)
     (:=
      (frame-val->path
       (cdr
        (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                        (dirname path))
                     (frame->frame frame))))
      (take
       (len
        (frame-val->path$inline
         (cdr (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
       (dirname path))
      :hints :none)
     (:change-goal nil t)
     (:dive 2)
     (:rewrite take-when-prefixp)
     :top
     (:bash ("goal" :in-theory (enable abs-mkdir-correctness-lemma-13)))
     :up
     (:=
      (append
       (append
        (take
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
         (dirname path))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
         (dirname path)))
       (list (basename path))))
     (:dive 1)
     (:claim
      (and
       (<=
        (len
         (frame-val->path
          (cdr (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                frame))))
        (len (dirname path)))))
     (:rewrite binary-append-take-nthcdr)
     :top :bash))

  (defthm
    abs-mkdir-correctness-lemma-185
    (implies
     (and
      (equal
       (mv-nth
        0
        (collapse
         (frame-with-root
          (frame->root (partial-collapse frame (dirname path)))
          (put-assoc-equal
           (abs-find-file-src (partial-collapse frame (dirname path))
                              (dirname path))
           (frame-val
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (frame->frame (partial-collapse frame (dirname path))))))
            (mv-nth
             0
             (abs-place-file-helper
              (frame-val->dir
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (frame->frame (partial-collapse frame (dirname path))))))
              (append
               (nthcdr
                (len
                 (frame-val->path
                  (cdr
                   (assoc-equal
                    (abs-find-file-src (partial-collapse frame (dirname path))
                                       (dirname path))
                    frame))))
                (dirname path))
               (list (basename path)))
              '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                (contents))))
            (frame-val->src
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (frame->frame (partial-collapse frame (dirname path)))))))
           (frame->frame (partial-collapse frame (dirname path)))))))
       (mv-nth
        0
        (abs-place-file-helper
         (mv-nth
          0
          (collapse
           (frame-with-root
            (frame->root (partial-collapse frame (dirname path)))
            (frame->frame (partial-collapse frame (dirname path))))))
         (append
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (frame->frame (partial-collapse frame (dirname path))))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path))
          (list (basename path)))
         '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (equal
       (mv-nth
        1
        (collapse
         (frame-with-root
          (frame->root (partial-collapse frame (dirname path)))
          (put-assoc-equal
           (abs-find-file-src (partial-collapse frame (dirname path))
                              (dirname path))
           (frame-val
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (frame->frame (partial-collapse frame (dirname path))))))
            (mv-nth
             0
             (abs-place-file-helper
              (frame-val->dir
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (frame->frame (partial-collapse frame (dirname path))))))
              (append
               (nthcdr
                (len
                 (frame-val->path
                  (cdr
                   (assoc-equal
                    (abs-find-file-src (partial-collapse frame (dirname path))
                                       (dirname path))
                    frame))))
                (dirname path))
               (list (basename path)))
              '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                (contents))))
            (frame-val->src
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (frame->frame (partial-collapse frame (dirname path)))))))
           (frame->frame (partial-collapse frame (dirname path)))))))
       (mv-nth
        1
        (collapse
         (frame-with-root
          (frame->root (partial-collapse frame (dirname path)))
          (frame->frame (partial-collapse frame (dirname path)))))))
      (equal
       (ctx-app
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (partial-collapse frame (dirname path)))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path))
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (mv-nth
         0
         (abs-place-file-helper
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (list (basename path))
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))))
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
         (dirname path)))
       (mv-nth
        0
        (abs-place-file-helper
         (ctx-app
          (mv-nth
           1
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 frame))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (find-new-index (strip-cars (partial-collapse frame (dirname path))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path)))
         (append
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
           (dirname path))
          (list (basename path)))
         '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (abs-fs-p fs)
      (m1-file-alist-p fs)
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (remove-assoc-equal
          (basename path)
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr
              (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (abs-find-file-src (partial-collapse frame (dirname path))
                                    (dirname path))
                 (partial-collapse frame (dirname path))))))
             (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))))))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))))
      (not
       (member-equal
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (abs-addrs
         (frame-val->dir
          (cdr (assoc-equal
                (abs-find-file-src (partial-collapse frame (dirname path))
                                   (dirname path))
                (partial-collapse frame (dirname path))))))))
      (prefixp
       (frame-val->path
        (cdr
         (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                         (dirname path))
                      frame)))
       (dirname path))
      (not (equal (abs-find-file-src (partial-collapse frame (dirname path))
                                     (dirname path))
                  0))
      (not
       (consp (names-at (frame->root (partial-collapse frame (dirname path)))
                        (dirname path))))
      (path-clear
       (dirname path)
       (remove-assoc-equal
        (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path))
        (frame->frame (partial-collapse frame (dirname path)))))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
      (not (equal (mv-nth 1
                          (hifat-find-file (mv-nth 0 (collapse frame))
                                           path))
                  0)))
     (frame-reps-fs
      (mv-nth 0 (abs-mkdir frame path))
      (mv-nth 0
              (hifat-place-file
               (mv-nth 0 (collapse frame))
               path
               (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                       t)
                        nil)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       nil
       ((:rewrite abs-mkdir-correctness-lemma-148)
        (:linear abs-mkdir-correctness-lemma-143)
        (:rewrite collapse-congruence-lemma-4)
        (:rewrite names-at-of-abs-place-file-helper-1)
        (:rewrite remove-assoc-of-put-assoc)
        (:rewrite abs-mkdir-correctness-lemma-155)
        (:rewrite abs-find-file-after-abs-mkdir-lemma-14)
        (:rewrite absfat-place-file-correctness-lemma-6)
        (:rewrite hifat-find-file-correctness-lemma-2)
        (:rewrite hifat-find-file-correctness-lemma-4)
        (:rewrite hifat-place-file-correctness-3)
        (:rewrite hifat-place-file-correctness-3)
        (:rewrite abs-find-file-helper-of-collapse-2 . 2)
        (:rewrite abs-place-file-helper-correctness-2)
        (:rewrite 1st-complete-of-put-assoc-2)
        (:rewrite cdr-of-append-when-consp)
        (:rewrite fat32-filename-p-of-car-when-fat32-filename-list-p)
        (:rewrite abs-no-dups-p-of-remove1-assoc)
        (:rewrite abs-mkdir-correctness-lemma-16 . 1)
        (:linear 1st-complete-of-put-assoc-1)
        (:rewrite subsetp-when-prefixp)
        (:rewrite car-of-true-list-list-fix-x-normalize-const-under-list-equiv)
        (:rewrite abs-find-file-helper-of-collapse-1 . 2)
        (:rewrite integer-listp-when-not-consp)
        (:rewrite absfat-equiv-implies-set-equiv-addrs-at-1-lemma-2)
        (:rewrite hifat-place-file-correctness-3)
        (:rewrite len-of-append)
        (:rewrite collapse-congruence-lemma-5)
        (:rewrite car-of-append)
        (:rewrite 1st-complete-of-put-assoc-lemma-1)
        (:rewrite 1st-complete-of-put-assoc-2)
        (:rewrite cdr-of-append-when-consp)
        (:rewrite fat32-filename-p-of-car-when-fat32-filename-list-p)
        (:rewrite member-of-strip-cars)
        (:rewrite remove-assoc-of-remove-assoc)
        (:rewrite absfat-subsetp-transitivity)
        (:rewrite abs-mkdir-correctness-lemma-64)
        (:rewrite hifat-file-alist-fix-guard-lemma-1)
        (:rewrite prefixp-transitive . 1))))))

  (defthm
    abs-mkdir-correctness-lemma-186
    (implies
     (and
      (equal
       (mv-nth
        1
        (abs-find-file-helper
         (frame-val->dir
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path)))))
         path))
       0)
      (equal
       (abs-find-file-helper
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
        (dirname path))
       (hifat-find-file
        (mv-nth 0
                (collapse (partial-collapse frame (dirname path))))
        (dirname path)))
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (m1-file-alist-p fs)
      (mv-nth 1 (collapse frame))
      (hifat-equiv (mv-nth 0 (collapse frame))
                   fs)
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path))))
      (consp (dirname path)))
     (consp
      (assoc-equal
       (basename path)
       (m1-file->contents (mv-nth 0
                                  (hifat-find-file fs (dirname path)))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (disable (:rewrite abs-mkdir-correctness-lemma-89))
      :use
      (:instance
       (:rewrite abs-mkdir-correctness-lemma-89)
       (y (list (basename path)))
       (x (dirname path))
       (fs
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path))))))))))

  (defthm
    abs-mkdir-correctness-lemma-187
    (implies
     (and
      (equal
       (mv-nth
        0
        (collapse
         (frame-with-root
          (frame->root (partial-collapse frame (dirname path)))
          (put-assoc-equal
           0 '((path) (dir) (src . 0))
           (frame->frame (partial-collapse frame (dirname path)))))))
       (mv-nth
        0
        (hifat-place-file
         (mv-nth 0
                 (collapse (partial-collapse frame (dirname path))))
         (dirname path)
         (m1-file
          (m1-file->dir-ent
           (mv-nth
            0
            (hifat-find-file
             (mv-nth 0
                     (collapse (partial-collapse frame (dirname path))))
             (dirname path))))
          (put-assoc-equal
           (basename path)
           '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (contents))
           (m1-file->contents
            (mv-nth
             0
             (hifat-find-file
              (mv-nth 0
                      (collapse (partial-collapse frame (dirname path))))
              (dirname path)))))))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root (partial-collapse frame (dirname path)))
         (put-assoc-equal
          0 '((path) (dir) (src . 0))
          (frame->frame (partial-collapse frame (dirname path)))))))
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (m1-file-alist-p fs)
      (mv-nth 1 (collapse frame))
      (hifat-equiv (mv-nth 0 (collapse frame))
                   fs)
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path))))
      (not
       (consp
        (assoc-equal
         (basename path)
         (m1-file->contents (mv-nth 0
                                    (hifat-find-file fs (dirname path)))))))
      (consp path))
     (absfat-equiv
      (mv-nth
       0
       (hifat-place-file
        (mv-nth
         0
         (collapse
          (frame-with-root
           (frame-val->dir
            (cdr (assoc-equal 0
                              (partial-collapse frame (dirname path)))))
           (frame->frame (partial-collapse frame (dirname path))))))
        path
        '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                   0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
          (contents))))
      (mv-nth
       0
       (hifat-place-file
        (mv-nth 0 (collapse frame))
        (dirname path)
        (m1-file
         (m1-file->dir-ent (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
         (put-assoc-equal
          (basename path)
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))
          (m1-file->contents
           (mv-nth 0
                   (hifat-find-file (mv-nth 0 (collapse frame))
                                    (dirname path))))))))))
    :instructions
    ((:in-theory (e/d (m1-file-contents-p-correctness-1)
                      nil))
     :promote
     (:= (frame-val->dir
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path)))))
         (frame->root (partial-collapse frame (dirname path)))
         :hints (("goal" :in-theory (enable frame->root))))
     :bash (:dive 1)
     :=
     (:claim
      (and
       (hifat-equiv (mv-nth 0
                            (collapse (partial-collapse frame (dirname path))))
                    (mv-nth 0 (collapse frame)))
       (hifat-no-dups-p
        (m1-file->contents$inline
         (m1-file
          (m1-file->dir-ent$inline
           (mv-nth
            0
            (hifat-find-file
             (mv-nth 0
                     (collapse (partial-collapse frame (dirname path))))
             (dirname path))))
          (put-assoc-equal
           (basename path)
           '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (contents))
           (m1-file->contents$inline
            (mv-nth
             0
             (hifat-find-file
              (mv-nth 0
                      (collapse (partial-collapse frame (dirname path))))
              (dirname path)))))))))
      :hints :none)
     (:rewrite hifat-place-file-correctness-4
               ((m1-file-alist1 (mv-nth 0 (collapse frame)))))
     (:claim
      (and
       (hifat-equiv
        (m1-file->contents$inline
         (m1-file
          (m1-file->dir-ent$inline
           (mv-nth
            0
            (hifat-find-file
             (mv-nth 0
                     (collapse (partial-collapse frame (dirname path))))
             (dirname path))))
          (put-assoc-equal
           (basename path)
           '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (contents))
           (m1-file->contents$inline
            (mv-nth
             0
             (hifat-find-file
              (mv-nth 0
                      (collapse (partial-collapse frame (dirname path))))
              (dirname path)))))))
        (m1-file->contents$inline
         (m1-file (m1-file->dir-ent$inline
                   (mv-nth 0
                           (hifat-find-file (mv-nth 0 (collapse frame))
                                            (dirname path))))
                  (put-assoc-equal
                   (basename path)
                   '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                     (contents))
                   (m1-file->contents$inline
                    (mv-nth 0
                            (hifat-find-file (mv-nth 0 (collapse frame))
                                             (dirname path))))))))
       (m1-directory-file-p
        (m1-file-fix$inline
         (m1-file
          (m1-file->dir-ent$inline
           (mv-nth
            0
            (hifat-find-file
             (mv-nth 0
                     (collapse (partial-collapse frame (dirname path))))
             (dirname path))))
          (put-assoc-equal
           (basename path)
           '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (contents))
           (m1-file->contents$inline
            (mv-nth
             0
             (hifat-find-file
              (mv-nth 0
                      (collapse (partial-collapse frame (dirname path))))
              (dirname path))))))))
       (m1-directory-file-p
        (m1-file-fix$inline
         (m1-file (m1-file->dir-ent$inline
                   (mv-nth 0
                           (hifat-find-file (mv-nth 0 (collapse frame))
                                            (dirname path))))
                  (put-assoc-equal
                   (basename path)
                   '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                              0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                     (contents))
                   (m1-file->contents$inline
                    (mv-nth 0
                            (hifat-find-file (mv-nth 0 (collapse frame))
                                             (dirname path)))))))))
      :hints :none)
     (:rewrite
      hifat-place-file-when-hifat-equiv-1
      ((file2
        (m1-file
         (m1-file->dir-ent (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
         (put-assoc-equal
          (basename path)
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))
          (m1-file->contents
           (mv-nth 0
                   (hifat-find-file (mv-nth 0 (collapse frame))
                                    (dirname path)))))))))
     :top :s
     (:bash ("goal" :in-theory (enable m1-file-contents-p-correctness-1)))
     (:change-goal nil t)
     (:bash ("goal" :in-theory (enable m1-file-contents-p-correctness-1)))
     (:dive 1)
     (:rewrite
      hifat-equiv-of-put-assoc-2
      ((fs2
        (m1-file->contents (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path)))))))
     :top :s
     :bash :bash
     :bash :bash
     :bash :bash
     :bash :bash))

  (defthm
    abs-mkdir-correctness-lemma-188
    (implies
     (and
      (not (equal (mv-nth 1 (hifat-find-file fs path))
                  0))
      (equal
       (abs-find-file-helper
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
        (dirname path))
       (hifat-find-file
        (mv-nth 0
                (collapse (partial-collapse frame (dirname path))))
        (dirname path)))
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (m1-file-alist-p fs)
      (mv-nth 1 (collapse frame))
      (hifat-equiv (mv-nth 0 (collapse frame))
                   fs)
      (abs-separate frame)
      (subsetp-equal (abs-addrs (frame->root frame))
                     (frame-addrs-root (frame->frame frame)))
      (equal (mv-nth 1 (hifat-find-file fs (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0 (hifat-find-file fs (dirname path)))))
     (>
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
        path))
      0))
    :rule-classes :linear
    :instructions (:promote (:dive 2 2 2)
                            (:= path
                                (append (dirname path)
                                        (list (basename path)))
                                :equiv fat32-filename-list-equiv$inline)
                            :up
                            (:rewrite abs-mkdir-correctness-lemma-89)
                            :top :bash (:contrapose 1)
                            (:dive 1 2 2)
                            (:= path
                                (append (dirname path)
                                        (list (basename path)))
                                :equiv fat32-filename-list-equiv$inline)
                            :up (:rewrite abs-mkdir-correctness-lemma-77)
                            :top :bash))

  (defthm
    abs-mkdir-correctness-lemma-189
    (implies
     (and
      (equal
       (mv-nth
        0
        (collapse
         (frame-with-root
          (frame->root (partial-collapse frame (dirname path)))
          (put-assoc-equal
           0
           (frame-val
            (frame-val->path
             (cdr (assoc-equal
                   0
                   (frame->frame (partial-collapse frame (dirname path))))))
            (mv-nth
             0
             (abs-place-file-helper
              (frame-val->dir
               (cdr
                (assoc-equal
                 0
                 (frame->frame (partial-collapse frame (dirname path))))))
              (append
               (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                       (dirname path))
               (list (basename path)))
              '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                (contents))))
            (frame-val->src
             (cdr
              (assoc-equal
               0
               (frame->frame (partial-collapse frame (dirname path)))))))
           (frame->frame (partial-collapse frame (dirname path)))))))
       (mv-nth
        0
        (abs-place-file-helper
         (mv-nth
          0
          (collapse
           (frame-with-root
            (frame->root (partial-collapse frame (dirname path)))
            (frame->frame (partial-collapse frame (dirname path))))))
         (append
          (frame-val->path
           (cdr (assoc-equal
                 0
                 (frame->frame (partial-collapse frame (dirname path))))))
          (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                  (dirname path))
          (list (basename path)))
         '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (equal
       (mv-nth
        1
        (collapse
         (frame-with-root
          (frame->root (partial-collapse frame (dirname path)))
          (put-assoc-equal
           0
           (frame-val
            (frame-val->path
             (cdr (assoc-equal
                   0
                   (frame->frame (partial-collapse frame (dirname path))))))
            (mv-nth
             0
             (abs-place-file-helper
              (frame-val->dir
               (cdr
                (assoc-equal
                 0
                 (frame->frame (partial-collapse frame (dirname path))))))
              (append
               (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                       (dirname path))
               (list (basename path)))
              '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                         0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
                (contents))))
            (frame-val->src
             (cdr
              (assoc-equal
               0
               (frame->frame (partial-collapse frame (dirname path)))))))
           (frame->frame (partial-collapse frame (dirname path)))))))
       (mv-nth
        1
        (collapse
         (frame-with-root
          (frame->root (partial-collapse frame (dirname path)))
          (frame->frame (partial-collapse frame (dirname path)))))))
      (equal
       (abs-find-file-helper
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))
        (nthcdr 0 (dirname path)))
       (abs-find-file (partial-collapse frame (dirname path))
                      (dirname path)))
      (equal
       (ctx-app
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                  (dirname path))
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (mv-nth
         0
         (abs-place-file-helper
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr (assoc-equal 0
                               (partial-collapse frame (dirname path)))))
            (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                    (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (list (basename path))
          '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
            (contents))))
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                (dirname path)))
       (mv-nth
        0
        (abs-place-file-helper
         (ctx-app
          (mv-nth
           1
           (abs-disassoc
            (frame-val->dir
             (cdr (assoc-equal 0
                               (partial-collapse frame (dirname path)))))
            (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                    (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr (assoc-equal 0
                               (partial-collapse frame (dirname path)))))
            (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                    (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))
          (find-new-index (strip-cars (partial-collapse frame (dirname path))))
          (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                  (dirname path)))
         (append (nthcdr (len (frame-val->path (cdr (assoc-equal 0 frame))))
                         (dirname path))
                 (list (basename path)))
         '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                    0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
           (contents)))))
      (fat32-filename-list-equiv (append (dirname path)
                                         (list (basename path)))
                                 path)
      (no-duplicatesp-equal (strip-cars frame))
      (frame-p frame)
      (equal (frame-val->src (cdr (assoc-equal 0 frame)))
             0)
      (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
      (abs-fs-p fs)
      (m1-file-alist-p fs)
      (frame-reps-fs frame fs)
      (consp (assoc-equal 0 frame))
      (not
       (consp
        (abs-addrs
         (remove-assoc-equal
          (basename path)
          (mv-nth
           0
           (abs-disassoc
            (frame-val->dir
             (cdr (assoc-equal 0
                               (partial-collapse frame (dirname path)))))
            (nthcdr 0 (dirname path))
            (find-new-index
             (strip-cars (partial-collapse frame (dirname path))))))))))
      (not
       (consp
        (abs-addrs
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file (partial-collapse frame (dirname path))
                                 (dirname path)))))))
      (not
       (member-equal
        (find-new-index (strip-cars (partial-collapse frame (dirname path))))
        (abs-addrs
         (frame-val->dir
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path))))))))
      (not
       (equal
        (mv-nth
         1
         (abs-disassoc
          (frame-val->dir
           (cdr (assoc-equal 0
                             (partial-collapse frame (dirname path)))))
          (dirname path)
          (find-new-index
           (strip-cars (partial-collapse frame (dirname path))))))
        (frame-val->dir
         (cdr (assoc-equal 0
                           (partial-collapse frame (dirname path)))))))
      (equal (abs-find-file-src (partial-collapse frame (dirname path))
                                (dirname path))
             0)
      (path-clear (dirname path)
                  (frame->frame (partial-collapse frame (dirname path))))
      (equal (mv-nth 1
                     (hifat-find-file (mv-nth 0 (collapse frame))
                                      (dirname path)))
             0)
      (m1-directory-file-p (mv-nth 0
                                   (hifat-find-file (mv-nth 0 (collapse frame))
                                                    (dirname path))))
      (not (equal (mv-nth 1
                          (hifat-find-file (mv-nth 0 (collapse frame))
                                           path))
                  0)))
     (frame-reps-fs
      (mv-nth 0 (abs-mkdir frame path))
      (mv-nth 0
              (hifat-place-file
               (mv-nth 0 (collapse frame))
               path
               (m1-file (dir-ent-install-directory-bit (dir-ent-fix nil)
                                                       t)
                        nil)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d
       nil
       ((:rewrite abs-mkdir-correctness-lemma-148)
        (:linear abs-mkdir-correctness-lemma-143)
        (:rewrite collapse-congruence-lemma-4)
        (:rewrite names-at-of-abs-place-file-helper-1)
        (:rewrite remove-assoc-of-put-assoc)
        (:rewrite abs-mkdir-correctness-lemma-155)
        (:rewrite abs-find-file-after-abs-mkdir-lemma-14)
        (:rewrite absfat-place-file-correctness-lemma-6)
        (:rewrite hifat-find-file-correctness-lemma-2)
        (:rewrite hifat-find-file-correctness-lemma-4)
        (:rewrite hifat-place-file-correctness-3)
        (:rewrite hifat-place-file-correctness-3)
        (:rewrite abs-find-file-helper-of-collapse-2 . 2)
        (:rewrite abs-place-file-helper-correctness-2)
        (:rewrite 1st-complete-of-put-assoc-2)
        (:rewrite cdr-of-append-when-consp)
        (:rewrite fat32-filename-p-of-car-when-fat32-filename-list-p)
        (:rewrite abs-no-dups-p-of-remove1-assoc)
        (:rewrite abs-mkdir-correctness-lemma-16 . 1)
        (:linear 1st-complete-of-put-assoc-1)
        (:rewrite subsetp-when-prefixp)
        (:rewrite car-of-true-list-list-fix-x-normalize-const-under-list-equiv)
        (:rewrite abs-find-file-helper-of-collapse-1 . 2)
        (:rewrite integer-listp-when-not-consp)
        (:rewrite absfat-equiv-implies-set-equiv-addrs-at-1-lemma-2)
        (:rewrite hifat-place-file-correctness-3)
        (:rewrite len-of-append)
        (:rewrite collapse-congruence-lemma-5)
        (:rewrite car-of-append)
        (:rewrite 1st-complete-of-put-assoc-lemma-1)
        (:rewrite 1st-complete-of-put-assoc-2)
        (:rewrite cdr-of-append-when-consp)
        (:rewrite fat32-filename-p-of-car-when-fat32-filename-list-p)
        (:rewrite member-of-strip-cars)
        (:rewrite remove-assoc-of-remove-assoc)
        (:rewrite absfat-subsetp-transitivity)
        (:rewrite abs-mkdir-correctness-lemma-64)
        (:rewrite hifat-file-alist-fix-guard-lemma-1)
        (:rewrite prefixp-transitive . 1)
        (:linear abs-mkdir-correctness-lemma-124)
        (:rewrite abs-mkdir-correctness-lemma-43)
        (:rewrite abs-disassoc-correctness-1)
        (:linear len-when-prefixp)
        (:definition remove-equal)
        (:rewrite abs-mkdir-correctness-lemma-47 . 2)
        (:rewrite abs-mkdir-correctness-lemma-100 . 2)
        (:rewrite hifat-file-alist-fix-when-hifat-no-dups-p)
        (:rewrite consp-of-assoc-of-frame->frame)
        (:rewrite prefixp-transitive . 2)
        (:rewrite prefixp-one-way-or-another . 2)
        (:rewrite car-of-nthcdr)
        (:rewrite abs-fs-fix-under-abs-fs-equiv)
        (:rewrite remove-assoc-when-absent-2)
        (:rewrite m1-regular-file-p-correctness-1)
        (:rewrite m1-file-alist-p-of-abs-place-file-helper)))))))

(defthm abs-mkdir-correctness-1
 (implies
  (and
   (no-duplicatesp-equal (strip-cars frame))
   (frame-p frame)
   (equal (frame-val->src$inline (cdr (assoc-equal 0 frame)))
          '0)
   (not (consp (frame-val->path$inline (cdr (assoc-equal 0 frame)))))
   (equal
    (len (frame-val->path
          (cdr (assoc-equal 0
                            (partial-collapse frame (dirname path))))))
    0)
   (abs-fs-p fs)
   (m1-file-alist-p fs)
   (frame-reps-fs frame fs)
   (consp (assoc-equal 0 frame))
   (not
    (consp
     (abs-addrs
      (remove-assoc-equal
       (basename path)
       (mv-nth
        0
        (abs-disassoc
         (frame-val->dir$inline
          (cdr
           (assoc-equal
            (abs-find-file-src (partial-collapse frame (dirname path))
                               (dirname path))
            (partial-collapse frame (dirname path)))))
         (nthcdr
          (len
           (frame-val->path$inline
            (cdr
             (assoc-equal
              (abs-find-file-src (partial-collapse frame (dirname path))
                                 (dirname path))
              (partial-collapse frame (dirname path))))))
          (dirname path))
         (find-new-index
          (strip-cars (partial-collapse frame (dirname path))))))))))
   (not
    (consp
     (abs-addrs
      (abs-file->contents$inline
       (mv-nth 0
               (abs-find-file (partial-collapse frame (dirname path))
                              (dirname path)))))))
   (not
    (member-equal
     (find-new-index (strip-cars (partial-collapse frame (dirname path))))
     (abs-addrs
      (frame-val->dir$inline
       (cdr (assoc-equal
             (abs-find-file-src (partial-collapse frame (dirname path))
                                (dirname path))
             (partial-collapse frame (dirname path))))))))
   (prefixp
    (frame-val->path$inline
     (cdr
      (assoc-equal (abs-find-file-src (partial-collapse frame (dirname path))
                                      (dirname path))
                   frame)))
    (dirname path))
   (not
    (equal
     (mv-nth
      1
      (abs-disassoc
       (frame-val->dir
        (cdr (assoc-equal 0
                          (partial-collapse frame (dirname path)))))
       (dirname path)
       (find-new-index
        (strip-cars (partial-collapse frame (dirname path))))))
     (frame-val->dir
      (cdr (assoc-equal 0
                        (partial-collapse frame (dirname path)))))))
   (if
    (equal (abs-find-file-src (partial-collapse frame (dirname path))
                              (dirname path))
           0)
    (path-clear (dirname path)
                (frame->frame (partial-collapse frame (dirname path))))
    (and
     (atom (names-at (frame->root (partial-collapse frame (dirname path)))
                     (dirname path)))
     (path-clear
      (dirname path)
      (remove-assoc-equal
       (abs-find-file-src (partial-collapse frame (dirname path))
                          (dirname path))
       (frame->frame (partial-collapse frame (dirname path))))))))
  (and (frame-reps-fs (mv-nth 0 (abs-mkdir frame path))
                      (mv-nth 0
                              (hifat-mkdir (mv-nth 0 (collapse frame))
                                           path)))
       (equal (mv-nth 2 (abs-mkdir frame path))
              (mv-nth 2
                      (hifat-mkdir (mv-nth 0 (collapse frame))
                                   path)))))
 :hints
 (("goal"
   :in-theory
   (union-theories '(length hifat-mkdir fat32-filename-p-of-basename
                            fat32-filename-p-correctness-1
                            str::coerce-to-list-removal
                            (:e m1-file-p)
                            (:e m1-regular-file-p)
                            (:e hifat-no-dups-p)
                            (:e m1-file->contents)
                            abs-mkdir-correctness-lemma-97
                            abs-mkdir-correctness-lemma-109
                            abs-mkdir-correctness-lemma-110
                            abs-mkdir-correctness-lemma-111
                            abs-mkdir-correctness-lemma-112
                            abs-mkdir-correctness-lemma-113
                            abs-mkdir-correctness-lemma-114
                            abs-mkdir-correctness-lemma-115
                            abs-mkdir-correctness-lemma-117
                            abs-mkdir-correctness-lemma-118
                            abs-mkdir-correctness-lemma-119
                            abs-mkdir-correctness-lemma-120
                            abs-mkdir-correctness-lemma-121
                            abs-mkdir-correctness-lemma-122
                            abs-mkdir-correctness-lemma-125
                            abs-mkdir-correctness-lemma-132
                            abs-mkdir-correctness-lemma-136
                            abs-mkdir-correctness-lemma-140
                            abs-mkdir-correctness-lemma-141
                            abs-mkdir-correctness-lemma-142
                            abs-mkdir-correctness-lemma-143
                            abs-mkdir-correctness-lemma-144
                            abs-mkdir-correctness-lemma-145
                            abs-mkdir-correctness-lemma-146
                            abs-mkdir-correctness-lemma-147
                            abs-mkdir-correctness-lemma-148
                            abs-mkdir-correctness-lemma-149
                            abs-mkdir-correctness-lemma-150
                            abs-mkdir-correctness-lemma-151
                            abs-mkdir-correctness-lemma-152
                            abs-mkdir-correctness-lemma-153
                            abs-mkdir-correctness-lemma-154
                            abs-mkdir-correctness-lemma-156
                            abs-mkdir-correctness-lemma-159
                            abs-mkdir-correctness-lemma-161
                            abs-mkdir-correctness-lemma-165
                            abs-mkdir-correctness-lemma-173
                            abs-mkdir-correctness-lemma-180
                            abs-mkdir-correctness-lemma-181
                            abs-mkdir-correctness-lemma-185
                            abs-mkdir-correctness-lemma-189)
                   (theory 'minimal-theory))
   :do-not-induct t
   :use
   ((:instance
     collapse-hifat-place-file-2
     (x (abs-find-file-src (partial-collapse frame (dirname path))
                           (dirname path)))
     (frame (frame->frame (partial-collapse frame (dirname path))))
     (path
      (append
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal
            (abs-find-file-src (partial-collapse frame (dirname path))
                               (dirname path))
            frame))))
        (dirname path))
       (list (basename path))))
     (file '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (contents)))
     (root (frame->root (partial-collapse frame (dirname path)))))
    (:instance abs-find-file-src-correctness-2
               (frame (partial-collapse frame (dirname path)))
               (path (dirname path)))
    (:instance
     (:rewrite abs-place-file-helper-of-ctx-app-1 . 1)
     (x-path
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               frame))))
       (dirname path)))
     (x
      (find-new-index (strip-cars (partial-collapse frame (dirname path)))))
     (file '((dir-ent 0 0 0 0 0 0 0 0 0 0 0 16
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (contents)))
     (path (list (basename path)))
     (fs
      (mv-nth
       0
       (abs-disassoc
        (frame-val->dir
         (cdr (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
        (nthcdr
         (len
          (frame-val->path
           (cdr
            (assoc-equal
             (abs-find-file-src (partial-collapse frame (dirname path))
                                (dirname path))
             frame))))
         (dirname path))
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path)))))))
     (abs-file-alist1
      (mv-nth
       1
       (abs-disassoc
        (frame-val->dir
         (cdr (assoc-equal
               (abs-find-file-src (partial-collapse frame (dirname path))
                                  (dirname path))
               (partial-collapse frame (dirname path)))))
        (nthcdr
         (len
          (frame-val->path
           (cdr
            (assoc-equal
             (abs-find-file-src (partial-collapse frame (dirname path))
                                (dirname path))
             frame))))
         (dirname path))
        (find-new-index
         (strip-cars (partial-collapse frame (dirname path))))))))
    abs-mkdir-correctness-lemma-50))))

;; (defthm abs-find-file-after-abs-mkdir-2
;;  (b*
;;      (((mv frame & mkdir-error-code)
;;        (abs-mkdir frame (path-to-fat32-path (explode "/tmp/docs")))))
;;    (implies
;;     (equal mkdir-error-code 0)
;;     (b*
;;         (((mv frame & &)
;;           (abs-mkdir frame (path-to-fat32-path (explode "/tmp/docs/pdf-docs"))))
;;          ((mv file error-code)
;;           (abs-find-file frame path)))
;;       (and
;;        (equal error-code 0)
;;        (m1-file-equiv
;;         file
;;         (make-m1-file :dir-ent (dir-ent-install-directory-bit (dir-ent-fix nil)
;;                                                               t)))))))
;;  :hints (("goal" :in-theory (enable abs-mkdir partial-collapse)
;;           :do-not-induct t)))
