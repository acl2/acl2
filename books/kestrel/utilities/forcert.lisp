; Forward Certification
;
; Given a starting set of books and a dependency graph,
; follows the dependency edges to compute a terminal fringe of dependent books
; and writes them to a file.
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/file-io-light/read-objects-from-file" :dir :system)
(include-book "kestrel/file-io-light/write-strings-to-file-bang" :dir :system)
(include-book "std/strings/suffixp" :dir :system)
(include-book "std/strings/strrpos" :dir :system)
(include-book "kestrel/fty/fty-omap" :dir :system)
(include-book "kestrel/fty/map" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "kestrel/typed-lists-light/append-all" :dir :system)
(include-book "centaur/depgraph/top" :dir :system)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cert-pathnamep ((pn stringp))
  :returns (y/n booleanp)
  (and (stringp pn) (str::strsuffixp ".cert" pn)))

(define strip-cert ((pn stringp))
  :returns (ret stringp)
  (let ((p (str::strrpos ".cert" (str-fix pn))))
    (if (null p)
        (str-fix pn)
      (str::subseq pn 0 p))))

(defun acl2-pathnamep (pn)
  (and (stringp pn) (str::strsuffixp ".acl2" pn)))

(defun lisp-pathnamep (pn)
  (and (stringp pn) (str::strsuffixp ".lisp" pn)))

(defun none-of-above-pnp (pn)
  (not (or (cert-pathnamep pn)
           (acl2-pathnamep pn)
           (lisp-pathnamep pn))))

;----------------

(define pathname-type-string ((pn stringp))
  :returns (ret stringp)
  (let ((last-dot (search "." pn :from-end t)))
    (if (natp last-dot)
        ;; todo: prove something to remove this extra check
        (if (< last-dot (length pn))
            ;; also todo: get rid of str-fix
            (str-fix (subseq pn (+ last-dot 1) (length pn)))
          "")
      "")))

(define just-cert-pns ((pns string-listp))
  :returns (cert-pns string-listp)
  (if (endp pns)
      nil
    (if (cert-pathnamep (first pns))
        (cons (strip-cert (first pns))
              (just-cert-pns (rest pns)))
      (just-cert-pns (rest pns)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap bookdeps
  :key-type string
  :val-type str::string-list
  :pred bookdepsp)

(define just-cert-pns ((pns string-listp))
  :returns (cert-pns string-listp)
  (if (endp pns)
      nil
    (if (cert-pathnamep (first pns))
        (cons (strip-cert (first pns))
              (just-cert-pns (rest pns)))
      (just-cert-pns (rest pns)))))

(define update-many ((alist alistp) (bd bookdepsp) (exceptions string-listp))
     :returns (ret bookdepsp :hyp :guard)
     :verify-guards nil
     (b* (((when (endp alist)) bd) ;(bookdeps-fix bd))
          ((cons key val) (first alist))
          ((unless (and (stringp key) (string-listp val)))
           nil) ;(er hard 'top-level "ERROR: wrong type of alist elements~%")
          ((unless (string-listp exceptions))
           nil) ;(er hard 'top-level "ERROR: wrong type of exceptions~%")
          (trimmed-key (strip-cert key))
          ((unless (stringp trimmed-key)) nil)
          (trimmed-val (just-cert-pns val))
          ((unless (string-listp trimmed-val)) nil)
          (trimmed-val-exceptions-removed (set-difference-equal trimmed-val exceptions))
          ((unless (string-listp trimmed-val-exceptions-removed)) nil)
          (rest-alist (cdr alist))
          ((unless (mbt (alistp rest-alist))) nil))
       (if (or ;; In my world, there are about 660 books that have no dependencies.
               ;; (I.e., they don't have any include-book or depends-on forms.)
               ;; We omit them here.
               (null trimmed-val-exceptions-removed)
               (member-equal trimmed-key exceptions))
           (update-many rest-alist bd exceptions)
         (omap::update trimmed-key trimmed-val-exceptions-removed
                       (update-many rest-alist bd exceptions))))
     ///
     (verify-guards update-many :guard-debug t))

(define make-bookdeps ((alist alistp) (exceptions string-listp))
  :short "Makes a cleaned-up book dependency map from a build dependency alist."
  ;; exceptions is a list of those books to omit.
  ;; The purpose is to remove aggregating books that the user might not
  ;; care to certify, because they could drag in a lot of other unrelated books.
  ;; The biggest example is "doc/top".
  :returns (bd bookdepsp :hyp :guard)
  (b* (((unless (alistp alist))
        nil)
       ((unless (no-duplicatesp (strip-cars alist) :test 'equal))
        ;; TODO: put out a real error message here
        nil))
    ;; Now we need to add the elements one at a time, so that they will be sorted.
    (update-many alist nil exceptions)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define makefile-deps-file-to-forward-alist ((makefile-deps-path stringp)
                                             (remove-targets string-listp)
                                             state)
  :returns (mv ret-val state)
  :verify-guards nil
  (b* (((mv erp deps-info state)
        (read-objects-from-file makefile-deps-path state))
       ((when (or erp (not (consp deps-info)) (not (alistp (car deps-info)))))
        (cw "~%ERROR: in makefile-deps-file-to-forward-alist: ~x0~%" erp)
        (mv nil state))
       (dep-map-from-file (cdr (assoc-eq :DEPENDENCY-MAP (car deps-info))))
       ((when (or (null dep-map-from-file)
                  (not (alistp dep-map-from-file))))
        (cw "~%ERROR: unexpected first form of file ~x0~%" makefile-deps-path)
        (mv nil state))

       (tidied-bookdeps (make-bookdeps dep-map-from-file remove-targets))
       (fast-bookdeps (make-fast-alist tidied-bookdeps))
       (forward-bookdeps (depgraph::invert fast-bookdeps)))
    (mv forward-bookdeps state))
  ///
  (verify-guards makefile-deps-file-to-forward-alist :guard-debug t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Calculate the fringe that can be passed to cert.pl

(define subset-with-no-deps ((books string-listp) (forward-deps alistp))
  :returns (subset string-listp :hyp :guard)
  (if (endp books)
      nil
    (let ((first-book (first books)))
      (if (null (cdr (assoc-equal first-book forward-deps)))
          (cons first-book (subset-with-no-deps (cdr books) forward-deps))
        (subset-with-no-deps (cdr books) forward-deps)))))

(define fringe-books-from ((books string-listp) (forward-deps alistp))
  :returns (fringe-books string-listp :hyp :guard)
  (let ((alldeps (depgraph::transdeps books forward-deps)))
    (if (string-listp alldeps)
        (subset-with-no-deps alldeps forward-deps)
      nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; If a book mainly just has include-book forms in it, with possibly
;; an xdoc topic as well, and especially if the books it includes
;; are diverse in nature (*1), and if the book itself
;; is not included by other non-aggregating books (*2)
;; then it is probably not the sort of book that we want to
;; certify in advance, because it could drag in a lot of other books
;; that we might not be interested in.
;; ----
;; (*1) By "diverse in nature", we mean that a focused specific proof attempt
;;      is unlikely to need all the books.  A small number of focused books
;;      grouped together with a "top" book is not enough to make the "top"
;;      book considered "aggregating".
;; (*2) it is usually not a good idea to do include-book of an aggregating
;;      book but sometimes it could be.  This case is probably not handled
;;      properly here and could use more attention.
;;
;; Some notes on candidate aggregating books:
;; * centaur/fty/top  - although it is focused, it brings in "visitor", that
;;   few people use, but it doesn't bring in very much.  Probably should
;;   not be an aggregating book.
;; * xdoc/top - this doesn't bring in too much and it is included all over,
;;   as one would expect.  Probably should not be an aggregating book.

(defconst *standard-aggregating-books*
  '("doc/top"
    "kestrel/top"
    "kestrel/doc"
    "kestrel/crypto/attachments/top"
    "kestrel/crypto/top"
    "kestrel/ethereum/semaphore/top"
    "kestrel/ethereum/top"
    "kestrel/number-theory/top"
    "kestrel/utilities/system/terms"
    "kestrel/utilities/top"
    "kestrel/zcash/gadgets/top"
    "kestrel/zcash/top"
    "quicklisp/top"
    "std/lists/top"
    "std/typed-lists/top"
    "std/util/top"
    "top"
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Not used, but it should probably accompany terminate-strings
(define interleave-strings ((strings string-listp)
                            (separator stringp))
  :returns (ret string-listp :hyp :guard)
  (if (endp strings)
      nil
    (if (endp (cdr strings))
        (cons (car strings) nil)
      (cons (car strings)
            (cons separator
                  (interleave-strings (cdr strings) separator))))))

(define terminate-strings ((strings string-listp)
                           (terminator stringp))
  :returns (ret string-listp :hyp :guard)
  (if (endp strings)
      nil
    (cons (car strings)
          (cons terminator
                (terminate-strings (cdr strings) terminator)))))

(defttag :write-strings)

(define write-lines-to-file ((strings-without-newlines string-listp)
                             (filename stringp)
                             state)
  :returns (mv something state)
  (write-strings-to-file! (terminate-strings strings-without-newlines
                                             ;; Presumptive line terminator
                                             *newline-string*)
                         filename
                         'top-level
                         state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define absolutify-book-path ((path stringp) state)
  :returns (mv (newpath stringp) state)
  (b* (((mv erp abs-acl2-root state) (getenv$ "ACL2_ROOT" state))
       ((unless (and (null erp)
                     (stringp abs-acl2-root)))
        (mv "" state)))
    (mv (concatenate 'string abs-acl2-root "/books/" path) state)))

;; Probably don't need this now, and besides, we should probably only call (getenv$ "ACL2_ROOT" state) once.
(define absolutify-book-paths ((paths string-listp) state)
  :returns (mv (newpaths string-listp) state)
  (if (endp paths)
      (mv nil state)
    (b* (((mv first-abs state) (absolutify-book-path (first paths) state))
         ((mv rest-abs state) (absolutify-book-paths (rest paths) state)))
      (mv (cons first-abs rest-abs) state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *standard-makefile-deps-filename* "build/Makefile-deps.lsp")

(define expand-forcert-targets-into ((target-books string-listp)
                                     (temp-file-name stringp)
                                     (exclude-aggregating-books? booleanp)
                                     state)
  :returns (state)
  ;; More consistency checking would be nice.
  (b* (((mv abs-makefile-deps-filename state) (absolutify-book-path *standard-makefile-deps-filename* state))
       ((mv forward-deps state) (makefile-deps-file-to-forward-alist
                                 abs-makefile-deps-filename
                                 (if exclude-aggregating-books?
                                   *standard-aggregating-books*
                                   '())
                                 state))
       ((unless (alistp forward-deps)) state)
       (fringe (fringe-books-from target-books forward-deps))
       ((mv ?something state) (write-lines-to-file fringe temp-file-name state)))
    state))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For debugging

(define expand-forcert-targets-into-returning-fordeps ((target-books string-listp)
                                                       (temp-file-name stringp)
                                                       (exclude-aggregating-books? booleanp)
                                                       state)
  :returns (mv stuff state)
  ;; More consistency checking would be nice.
  (b* (((mv abs-makefile-deps-filename state) (absolutify-book-path *standard-makefile-deps-filename* state))
       ((mv forward-deps state) (makefile-deps-file-to-forward-alist
                                 abs-makefile-deps-filename
                                 (if exclude-aggregating-books?
                                   *standard-aggregating-books*
                                   '())
                                 state))
       ((unless (alistp forward-deps)) (mv (list :not-alist forward-deps) state))
       (fringe (fringe-books-from target-books forward-deps))
       ((mv ?something state) (write-lines-to-file fringe temp-file-name state)))
    (mv forward-deps state)))


#||
;; To see what happens:
(include-book
   "kestrel/utilities/forcert" :dir :system)
(include-book
  "std/util/defconsts" :dir :system)
(std::defconsts (*fordeps* state)
                (EXPAND-FORCERT-TARGETS-INTO-RETURNING-FORDEPS  '("kestrel/number-theory/tonelli-shanks" "kestrel/crypto/keccak/keccak") "/tmp/somefiles" NIL state))
||#
