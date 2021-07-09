; A tool to set many classes in a class-table
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "misc/records" :dir :system)
(include-book "class-tables")

;; An alternative to using a nest of many calls to S when there are many classes

(defund set-class-info (class-name class-info class-table)
  (declare (xargs :guard t)) ;strengthen?
  (s class-name class-info class-table))

(defthm get-class-info-of-set-class-info-same
  (equal (get-class-info class-name (set-class-info class-name class-info class-table))
         class-info)
  :hints (("Goal" :in-theory (enable get-class-info set-class-info))))

(defthm get-class-info-of-set-class-info-diff
  (implies (not (equal class-name1 class-name2))
           (equal (get-class-info class-name1 (set-class-info class-name2 class-info class-table))
                  (get-class-info class-name1 class-table)))
  :hints (("Goal" :in-theory (enable get-class-info set-class-info))))

(defthm get-class-info-of-set-class-info
  (equal (get-class-info class-name1 (set-class-info class-name2 class-info class-table))
         (if (equal class-name1 class-name2)
             class-info
           (get-class-info class-name1 class-table)))
  :hints (("Goal" :in-theory (enable get-class-info set-class-info))))

(defthm bound-in-class-tablep-of-set-class-info
  (equal (bound-in-class-tablep class-name1 (set-class-info class-name2 class-info class-table))
         (if (equal class-name1 class-name2)
             (if class-info t nil)
           (bound-in-class-tablep class-name1 class-table)))
  :hints (("Goal" :in-theory (enable bound-in-class-tablep set-class-info))))

;; ALIST pairs class-names with class-infos.  It may often be a constant.
(defund set-classes (alist class-table)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      class-table
    (let ((entry (first alist)))
      (set-class-info (car entry) ;; the class-name
                      (cdr entry) ;; the class-info
                      (set-classes (rest alist) class-table)))))

;rename
(defthm get-class-info-of-set-classes
  (implies (alistp alist)
           (equal (get-class-info class-name (set-classes alist class-table))
                  (let ((res (assoc-eq class-name alist)))
                    (if res
                        (cdr res)
                      (get-class-info class-name class-table)))))
  :hints (("Goal" :in-theory (enable set-classes))))

;; ;dup in axe
;; (DEFUN acl2::ALL-CONSP (acl2::X)
;;   (IF (ATOM acl2::X)
;;       T
;;       (AND (CONSP (FIRST acl2::X))
;;            (acl2::ALL-CONSP (REST acl2::X)))))

;; (defthm rkeys-of-set-classes
;;   (implies (acl2::all-consp (strip-cdrs alist))
;;            (equal (acl2::rkeys (set-classes alist class-table))
;;                   (set::union (list::2set (strip-cars alist))
;;                               (acl2::rkeys class-table))))
;;   :hints (("Goal" :in-theory (enable set-classes))))

;; (defthm in-of-rkeys-of-set-classes-when-not-assoc-equal
;;   (implies (and (not (assoc-equal class-name alist))
;;                 class-name)
;;            (equal (set::in class-name (acl2::rkeys (set-classes alist class-table)))
;;                   (set::in class-name (acl2::rkeys class-table))))
;;   :hints (("Goal" :in-theory (enable set-classes))))

;; (defthm in-of-rkeys-of-set-classes-when-assoc-equal
;;   (implies (and (assoc-equal class-name alist)
;;                 ;;class-name
;;                 )
;;            (equal (set::in class-name (acl2::rkeys (set-classes alist class-table)))
;;                   (if (cdr (assoc-equal class-name alist)) t nil)))
;;   :hints (("Goal" :in-theory (enable set-classes))))

;; (local
;;  (defthm strip-cdrs-of-cdr
;;    (equal (strip-cdrs (cdr alist))
;;           (cdr (strip-cdrs alist)))))

(local (in-theory (disable strip-cars strip-cdrs)))

;; (local
;;  (defthm memberp-of-strip-cars-iff
;;    (implies (alistp alist)
;;             (iff (memberp key (strip-cars alist))
;;                  (assoc-equal key alist)))
;;    :hints (("Goal" :in-theory (enable memberp assoc-equal strip-cars)))))

(defthm bound-in-class-tablep-of-set-classes
  (implies class-name
           (equal (bound-in-class-tablep class-name (set-classes alist class-table))
                  (let ((res (assoc-equal class-name alist)))
                    (if res
                        (if (cdr res) t nil)
                      (bound-in-class-tablep class-name class-table)))))
  :hints (("Goal" :in-theory (enable set-classes))))
