; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>


#||

bookdoc.lsp

This script loads the ACL2 and XDOC documentation for many ACL2 libraries, and
saves a unified manual into acl2/books/xdoc/bookdoc.  An important feature is
that it actually works even when all of the ACL2 books are uncertified, so you
don't have to wait for a regression to finish before generating the library
documentation.

Few ACL2 books have any documentation, and this script misses a few books that
do have some documentation:

  - I intentionally omit the workshop books.
  - I'm omitting the COI books since they have some loading problems.
  - The SULFA books seem to have some loading problems.
  - The clause-processors/basic-examples book has loading problems.

The basic strategy for To avoid book incompatibilities, I basically locally
include each book, then use make-event to save its extracted documentation
Because of this, we shouldn't need to worry (much) about name clashes, theory
incompatibilities, etc.

Well, there are still some (very) rough edges.

First, the script doesn't have any smart way of knowing what books have
documentation.  Instead, to get started, I just ran:

     grep -c -i ":Doc-Section" \
        `find . -name "*.lisp"` \
        `find . -name "*.lsp"` \
        `find . -name "*.acl2"` | grep -v :0

And then looked at the books it found.  This is obviously not future-proof, so
if someone adds some documentation to a new library in the future, it won't be
included in the unified manual until this file is updated.

Second, the script needs to explicitly load all of the packages involved in the
process ahead of time.  There are two reasons for this.  First, if we're
including uncertified books, ACL2 isn't smart enough to look at the
corresponding .acl2 file to read the packages it needs.  Second, even if we are
loading certified books, trying to save doc topics in a package that is only
locally defined results in interning errors.

We save the extracted documentation into book-documentation.lisp, which is
automatically loaded (if present) into the XDOC database when the :xdoc
and :save commands are executed.

||#

; In case ACL2 starts up outside its loop (formerly true for Lispworks):
;(acl2::value :q)
;(acl2::lp)

(in-package "ACL2")
(include-book "extra-packages")
(include-book "xdoc-impl/import-acl2doc" :dir :system)


(table book-doc 'doc nil)

(defun get-book-doc-table (world)
  (cdr (assoc-eq 'doc (table-alist 'book-doc world))))

(defmacro extract-documentation-from-book (bookname &key dir)
  `(with-output :off (event summary)
     (encapsulate
       ()
       (with-output :on (summary)
         (local (include-book ,bookname :dir ,dir)))
       (make-event
        (mv-let (er val state)
          (time$ (acl2::write-xdoc-alist :skip-topics xdoc::*acl2-ground-zero-names*)
                 :msg "; Importing :doc topics took ~st sec, ~sa bytes~%"
                 :mintime 1)
          (declare (ignore er val))
          (let ((topics (acl2::f-get-global 'acl2::xdoc-alist state)))
            (value `(table book-doc 'doc
                           (acons ,,bookname ',topics
                                  (get-book-doc-table world))))))))))

(defun extract-documentation-from-books-fn (booknames dir)
  (if (atom booknames)
      nil
    (cons `(extract-documentation-from-book ,(car booknames) :dir ,dir)
          (extract-documentation-from-books-fn (cdr booknames) dir))))

(defmacro extract-documentation-from-books (booknames &key dir)
  (cons 'progn (extract-documentation-from-books-fn booknames dir)))

;; I get errors on these
;; (extract-documentation-from-books
;;  ("coi/records/fast/private"
;;   "coi/records/fast/memory"
;;   "coi/adviser/adviser"
;;   "coi/defstructure/defstructure"
;;   "coi/defstructure/defstructure-definitions")
;;  :dir :system)

(extract-documentation-from-books
 ("ihs/ihs-theories"
  "ihs/logops-definitions"
  "ihs/quotient-remainder-lemmas"
  "ihs/logops-lemmas"
  "ihs/ihs-definitions"
  "ihs/ihs-lemmas"
  "ihs/ihs-init"
  "ihs/math-lemmas"
  "ihs/@logops")
 :dir :system)

(extract-documentation-from-books
 ("str/top")
 :dir :system)

(extract-documentation-from-books
 ("tools/bstar"
  "tools/safe-case"
  "tools/pattern-match"
  "tools/defevaluator-fast"
  "tools/do-not"
  "tools/defconsts"
  "tools/oracle-eval"
  "tools/defsum")
 :dir :system)

(extract-documentation-from-books
 ("misc/trace-star"
  "misc/hons-help"
  "misc/expander"
  "misc/defmac"
  "misc/qi-correct"
  "misc/meta-lemmas"
  "misc/defopener"
  "misc/dump-events"
  "misc/definline"
  "misc/sin-cos"
  "misc/untranslate-patterns"
  "misc/qi")
 :dir :system)

(extract-documentation-from-books
 ("data-structures/defalist"
  "data-structures/deflist"
  "data-structures/structures"
  "data-structures/utilities"
  "data-structures/array1"
  "data-structures/memories/private"
  "data-structures/memories/memory")
 :dir :system)

(extract-documentation-from-books
 ("hints/consider-hint")
 :dir :system)

;; This book has some problems.  First, we can't localize it due to defaxioms.
;; Second, we can't even include it normally unless it's certified, or it
;; seems to hit weird errors in make-event exapnsion.  So, I'm omitting it.
;; (include-book "clause-processors/basic-examples" :dir :system)

(extract-documentation-from-books
 ("clause-processors/SULFA/books/bv-smt-solver/bv-lib-definitions"
  ;; These sulfa books cause errors about a missing file, at least
  ;; without certification...
  ;; "clause-processors/SULFA/books/sat-tests/tutorial"
  ;; "clause-processors/SULFA/books/sat-tests/benchmark"
  ;; "clause-processors/SULFA/books/sat-tests/test-incremental"
  "clause-processors/autohide"
  )
 :dir :system)

(extract-documentation-from-books
 ("tools/safe-case"
;;  "tools/flag" -- switched to xdoc
  "tools/def-functional-instance"
  "tools/include-raw"
  "tools/pattern-match"
  "tools/bstar"
  "tools/defevaluator-fast"
  "tools/do-not"
  "tools/defconsts"
  "tools/oracle-eval"
  "tools/defsum")
 :dir :system)

(extract-documentation-from-books
 ("serialize/serialize")
 :dir :system)

(extract-documentation-from-books
 ("make-event/defconst-fast-examples")
 :dir :system)

;; I don't want to include the workshop books.
;; (extract-documentation-from-books
;;  ("workshops/1999/embedded/Proof-Of-Contribution/private-qr-lemmas"
;;   "workshops/1999/embedded/Exercises/Exercise1-2/private-qr-lemmas"
;;   "workshops/1999/de-hdl/de4"
;;   "workshops/2000/ruiz/multiset/defmul"
;;   "workshops/2003/gamboa-cowles-van-baalen/support/kalman-defs"
;;   "workshops/2006/swords-cook/lcsoundness/pattern-match"
;;   "workshops/2006/swords-cook/lcsoundness/defsum"
;;   "workshops/2006/hunt-reeber/support/bdd"
;;   "workshops/2006/hunt-reeber/support/sat"
;;   "workshops/2006/hunt-reeber/support/acl2"
;;   "workshops/2007/rubio/support/multisets/defmul"
;;   "workshops/2007/dillinger-et-al/code/hacker"
;;   "workshops/2007/dillinger-et-al/code/bridge"
;;   "workshops/2007/dillinger-et-al/code/subsumption"
;;   "workshops/2007/schmaltz/genoc-v1.0/instantiations/interfaces/bi-phi-m"
;;   )
;;  :dir :system)

(extract-documentation-from-books
 ("cowles/acl2-asg"
  "cowles/acl2-crg"
  "cowles/acl2-agp")
 :dir :system)

(extract-documentation-from-books
 ("hacking/hacker"
  "hacking/bridge"
  "hacking/subsumption")
 :dir :system)



(include-book "tools/defconsts" :dir :system)
(include-book "finite-set-theory/osets/sets" :dir :system)
(include-book "unicode/flatten" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)

(defconsts *merged-book-doc*
  (sets::mergesort
   (flatten (strip-cdrs (get-book-doc-table (w state))))))




;; Well, I guess we should also get books with XDOC documentation.

(include-book "cutil/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "finite-set-theory/osets/osets" :dir :system)
(include-book "str/top" :dir :system)


;; Okay, now the code to process what we've just loaded.

(program)

(defun stupid-find-files (topic book-doc-table)
  ;; Walk over the book-doc-table and find all files that included this topic.
  (cond ((atom book-doc-table)
         nil)
        ((member-equal topic (cdar book-doc-table))
         (cons (caar book-doc-table)
               (stupid-find-files topic (cdr book-doc-table))))
        (t
         (stupid-find-files topic (cdr book-doc-table)))))

(defun stupid-annotate-topics (topics book-doc-table)
  (if (atom topics)
      nil
    (let ((files  (stupid-find-files (car topics) book-doc-table))
          (long   (or (cdr (assoc :long (car topics))) "")))
      (cons (acons :long
                   (concatenate 'string long
                                "<p>[Imported by bookdoc from <tt>" (car files) "</tt>]</p>")
                   (xdoc::remove-alist-key :long (car topics)))
            (stupid-annotate-topics (cdr topics) book-doc-table)))))

(defconsts *annotated-doc*
  (stupid-annotate-topics *merged-book-doc* (get-book-doc-table (w state))))

#!XDOC
(table xdoc 'doc
       (sets::mergesort
        (append acl2::*annotated-doc* (get-xdoc-table world))))



;; Now check for documentation collisions.

(defun warn-about-collisions1 (collision-names topics)
  (cond ((atom topics)
         nil)
        ((not (member (cdr (assoc :name (car topics))) collision-names))
         (cons (car topics)
               (warn-about-collisions1 collision-names (cdr topics))))
        (t
         (let* ((long (cdr (assoc :long (car topics))))
                (long (concatenate 'string "<h4>Error: Multiple documentation
topics share this name.  We have arbitrarily chosen one of them.</h4>" long))
                (new-topic (acons :long long (xdoc::remove-alist-key :long (car topics)))))
           (cons new-topic
                 (warn-about-collisions1 collision-names (cdr topics)))))))

(defun warn-about-collisions (topics)
  (let ((dupes (duplicated-members (xdoc::all-topic-names topics))))
    (if dupes
        (prog2$
         (cw "Oops, conflicting documentation for ~&0.~%" dupes)
         (warn-about-collisions1 dupes topics))
      topics)))

(defconsts *book-documentation*
  (xdoc::remove-topics-by-name (warn-about-collisions (xdoc::get-xdoc-table (w state)))
                               xdoc::*acl2-ground-zero-names*))


;; This writing must be done relative to the ACL2 package!!!!!  See also
;; maybe-import-bookdoc.

(in-package "ACL2")
(defttag write-book-documentation)
(b* ((- (cw "Writing bookdoc.dat~%"))
     ((mv channel state)
      (open-output-channel! "bookdoc.dat" :character state))
     (state (princ$ "; GENERATED FILE -- DO NOT HAND EDIT" channel state))
     (state (newline channel state))
     (state (newline channel state))
     (state (fms! "~x0~%" (list (cons #\0 *book-documentation*)) channel state nil))
     (state (newline channel state))
     (state (close-output-channel channel state)))
  state)



