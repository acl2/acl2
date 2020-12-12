; A tool for speeding up lookups in lists during rewriting
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "reverse-list-def")
(include-book "kestrel/utilities/split-list-fast" :dir :system)
(local (include-book "member-equal"))
(local (include-book "reverse-list"))
(local (include-book "len"))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp2" :dir :system))
(local (include-book "kestrel/utilities/split-list-fast-rules" :dir :system))
(local (include-book "kestrel/utilities/merge-sort-symbol-less-than" :dir :system))

;; Logically equal to (append x y).  This can help avoid linear-time lookups
;; (via rewriting) in large symbolic lists by using the key to choose which
;; half of the list to look in.  See the rules
;; member-equal-of-append-with-key-first-half and
;; member-equal-of-append-with-key-second-half.
(defund append-with-key (key x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y)))
           (ignore key))
  (append x y))

;; Restrict the search for VAR to the branch (namely, X) where we know it is.
(defthm member-equal-of-append-with-key-first-half
  (implies (and (syntaxp (and (symbolp var)
                              (quotep key)
                              (symbolp (unquote key))
                              (symbol-< var (unquote key))))
                (member-equal var x))
           (member-equal var (append-with-key key x y)))
  :hints (("Goal" :in-theory (enable append-with-key))))

;; Restrict the search for VAR to the branch (namely, Y) where we know it is.
(defthm member-equal-of-append-with-key-second-half
  (implies (and (syntaxp (and (symbolp var)
                              (quotep key)
                              (symbolp (unquote key))
                              (not (symbol-< var (unquote key)))))
                (member-equal var y))
           (member-equal var (append-with-key key x y)))
  :hints (("Goal" :in-theory (enable append-with-key))))

;; test:
(thm
 (member-equal x (append-with-key 'y ;; causes the search for x to use the first half
                                  (append-with-key 'x (list w) (list x))
                                  (append-with-key 'z (list y) (list z))))
 :hints (("Goal" :in-theory (disable))))


;; The point of these scheme is to allow using a single assumption, that can be
;; searched in logarithmic time, to represent a large set of assumptions.
(defund make-append-with-key-nest-aux (vars)
  (declare (xargs :guard (and (symbol-listp vars)
                              (consp vars))
                  :measure (len vars)))
  (if (not (consp (rest vars)))
      ;; just one var
      `(cons ,(first vars) 'nil)
    ;; at least two vars:
    (mv-let (first-half-rev second-half)
      (split-list-fast vars)
      (let* ((first-half (reverse-list first-half-rev))
             (key (first second-half)))
        `(append-with-key ',key ;note that the key is quoted
                          ;; all are symbol-< than the key:
                          ,(make-append-with-key-nest-aux first-half)
                          ;; none are symbol-< than the key:
                          ,(make-append-with-key-nest-aux second-half))))))

(defthm pseudo-termp-of-make-append-with-key-nest-aux
  (implies (symbol-listp vars)
           (pseudo-termp (make-append-with-key-nest-aux vars)))
  :hints (("Goal" :in-theory (enable make-append-with-key-nest-aux))))

(defund make-append-with-key-nest (vars)
  (declare (xargs :guard (and (symbol-listp vars)
                              (consp vars))))
  (make-append-with-key-nest-aux (merge-sort-symbol-< vars)))

(defthm pseudo-termp-of-make-append-with-key-nest
  (implies (symbol-listp vars)
           (pseudo-termp (make-append-with-key-nest vars)))
  :hints (("Goal" :in-theory (enable make-append-with-key-nest))))
