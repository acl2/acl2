; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See README for an overview of the algorithm implemented by this file, and see
; write-td-cands.lsp for how it is invoked.  The fundamental idea is to include
; this book after including a book with many termination theorems underneath it
; -- normally, community book doc/top.lisp -- and then invoke td-init and
; write-td to build the termination-database and write it out, respectively.

(in-package "ACL2")

(include-book "fms-bang-list")
(include-book "strict-merge-sort")
(include-book "subsetp-eq-linear")
(include-book "termination-database-utilities")
(defttag :termination-database)
(set-register-invariant-risk nil)
(defttag nil)
(program)

(defun make-sysfile (filename system-books-dir)

; This is based on ACL2 source function filename-to-sysfile, but takes the
; value of (f-get-global 'system-books-dir state) instead of taking state.  If
; filename is under the given directory, then we return a sysfile (:system
; . path), where path is a relative pathname that is relative to that
; directory.  Otherwise, we return filename unchanged.

  (declare (xargs :mode :logic
                  :guard (and (stringp filename)
                              (stringp system-books-dir)
                              (<= (length system-books-dir) (fixnum-bound)))))
  (relativize-book-path filename system-books-dir :make-cons))

(defun td-book-alist (rev-wrld path system-books-dir acc)

; Rev-wrld is a reversed ACL2 world; thus, we are traversing it in the original
; chronological order.  Path is nil at the top level, and otherwise is the
; value of world global 'include-book-path at the current point of our
; traversal.  System-books-dir is a directory, intended to be a value of
; (f-get-global 'system-books-dir state).  We accumulate into acc an alist that
; associates each function symbol with the book in which it was introduced.
; Finally we return the accumulated alist as a fast-alist.

; At one point during development, calling this function up front cut almost
; 3/4 of the time from td-init.

  (declare (xargs :guard (and (plist-worldp rev-wrld)
                              (alistp acc))))
  (cond
   ((endp rev-wrld) (make-fast-alist acc))
   (t (let ((trip (car rev-wrld)))
        (cond
         ((and (eq (car trip) 'include-book-path)
               (eq (cadr trip) 'global-value))
          (td-book-alist (cdr rev-wrld) (cddr trip) system-books-dir acc))
         ((eq (cadr trip) 'formals)
          (td-book-alist (cdr rev-wrld)
                         path
                         system-books-dir
                         (let ((sysfile (and (consp path)
                                             (make-sysfile
                                              (remove-lisp-suffix (car path) t)
                                              system-books-dir))))
                           (acons (car trip)

; We store normed strings, anticipating their use as keys in a fast-alist.
; Probably this isn't necessary, since the call of make-fast-alist at the end
; should take care of that.

                                  (hons-copy sysfile)
                                  acc))))
         (t (td-book-alist (cdr rev-wrld) path system-books-dir acc)))))))

(defconst *fns-length-shift*

; This number is simply to shrink the fns array of td.  We choose -4 rather
; arbitrarily; so, in principle, 2^4 = 16 function symbols could go into (fnsi
; n td) for a given n.  In general fewer than 16 will be there, in part because
; many events aren't definitions, and in part because we are only including
; function symbols whose definitions are singly recursive.

; Quite possibly we could increase or decrease this constant substantially
; without ill effect, and perhaps even with a bit of a performance boost.

  -4)

(defstobj td ; termination database

; WARNING: Keep this in sync with td-reset.

; Our termination database stores termination clause-lists, each of them
; simplified a bit ("normalized").

; This database is represented by a stobj, td, with two array fields:

; - td-entry-ar: Each array element is a td-entry record, which consists of a
;   clause-list (as described above) and other information; see td-entry.  The
;   index of that entry (record) is called its "ID".  We may also refer to fn
;   as the "root" of the entry and, of course, we may also refer to the
;   clause-list of all-fns of the entry.

; - fns: Each entry is an alist, where each key is a logic-mode function
;   symbol, which is mapped to the list of all indices (IDs) of td-entry
;   records whose clause-list has at least one occurrence of that function
;   symbol.

; The stobj also has a next-index value, which is the first index that has
; never been used for td-entry-ar, initially 0.  It also has a "free list" of
; indices that are available because their entries have been essentially
; deleted.

; Each time the database is queried with a new function and corresponding
; termination clause-list, one of three things happens, as follows.

; - If the given clause-list is subsumed by a clause-list of an entry in the
;   database, then the root function of that entry is returned.

; NOTE: if we prefer not to update the database, for example because we do not
; want to return it, then we can stop here, returning nil to indicate failure.

; - Else if a clause-list of an entry subsumes the given clause-list, then the
;   database is updated: the entry is updated using the new function and
;   clause-list.

; - Otherwise a new entry is created for the given function and clause-list.

; WARNING: We assume that the initial value of fns-length-shifted, currently
; 16000, is (ash n (- *fns-length-shift*)) where n is the common dimension of
; td-entry-ar and fns, which is 1000 below.

  (td-entry-ar
   :type (array t (1000)) ; see WARNING above
   :resizable t
   :initially nil)
  (fns ; each entry is an alist whose keys all have the same td-fn-index
   :type (array t (1000)) ; see WARNING above
   :resizable t
   :initially nil)

; Next-index is the least td-entry-ar index such that it and all greater are
; unused.  However, there can be "holes": indices less than next-index that are
; mapped to nil.  These indices constitute the free-list.

  (next-index
   :initially 0)
  (free-list :initially nil)
  (fns-length-shifted :initially 16000) ; see WARNING above
  (book-alist)
  :non-memoizable t)

(defun td-array-entry-ar-reset (n td)
  (declare (xargs :stobjs td))
  (cond ((zp n) td)
        (t (let* ((n (1-f n))
                  (td (update-td-entry-ari n nil td)))
             (td-array-entry-ar-reset n td)))))

(defun td-fns-reset (n td)
  (declare (xargs :stobjs td))
  (cond ((zp n) td)
        (t (let* ((n (1-f n))
                  (td (update-fnsi n nil td)))
             (td-fns-reset n td)))))

(defun td-reset (td)
  (declare (xargs :stobjs td))
  (let* ((td (td-array-entry-ar-reset (next-index td) td))
         (td (td-fns-reset (fns-length td) td))
         (td (update-next-index 0 td))
         (td (update-free-list nil td))
         (td (update-fns-length-shifted 16000 td))
         (td (update-book-alist nil td)))
    td))

(defrec td-entry ; termination database entry

; This record includes the set of function symbols occurring in the associated
; clause-list; a function symbol, root, for which the clause-list is the
; termination clause-list; and the book containing the definition of root (nil,
; if root is defined in the boot-strap, else an ordered list whose car is the
; book containing the definition of root).  It also contains the measure and
; well-founded-relation of the :root function and an alt-alist with key-value
; pairs (f . B), where f is a function whose termination clause-list is
; subsumption-equivalent to the :clause-list and B is the book in which f is
; defined.

  (fns
   clause-list
   (root . book)
   . alt-alist)
  t)

(defun td-fn-index (fn wrld)
  (ash (getpropc fn 'absolute-event-number nil wrld)
       *fns-length-shift*))

(defun td-fn-id-list (fn wrld td)
  (declare (xargs :stobjs td))
  (let ((index (td-fn-index fn wrld)))
    (cdr (assoc-eq fn (fnsi index td)))))

(defun td-ids-filter-by-subset-of-1 (id-lst fns td acc)

; Accumulate into acc all ids (indices into the td-entry-ar array of the stobj
; td) in id-lst whose functions are subsets of fns (and hence, since fns is
; assumed to be non-empty, contain at least one function in fns).

  (declare (xargs :stobjs td))
  (cond ((endp id-lst) acc)
        (t (td-ids-filter-by-subset-of-1
            (cdr id-lst) fns td
            (let* ((id (car id-lst))
                   (entry (td-entry-ari id td))
                   (fns2 (access td-entry entry :fns)))
              (cond ((subsetp-eq-linear fns2 fns)

; We could use add-to-set here, but instead we prefer an n*log(n) algorithm, so
; we wait till the end (in td-ids-filter-by-subset-of) to eliminate duplicates.

                     (cons id acc))
                    (t acc)))))))

(defun td-ids-filter-by-subset-of (fns-tail fns wrld td acc)

; Accumulate into acc all ids of clause-lists whose functions are subsets of
; fns.

  (declare (xargs :stobjs td))
  (cond ((endp fns-tail)
         (strict-merge-sort-< acc)) ; eliminate duplicates
        (t (td-ids-filter-by-subset-of
            (cdr fns-tail) fns wrld td
            (td-ids-filter-by-subset-of-1
             (td-fn-id-list (car fns-tail) wrld td)
             fns td acc)))))

(defconst *td-book-failed* :failed)

(defun td-book (fn td)
  (declare (xargs :stobjs td))
  (let ((pair (hons-get fn (book-alist td))))
    (if pair (cdr pair) *td-book-failed*)))

(defun td-query-subsumer-1 (ids init-subsumes-count cl-list fn fn-book fns td)

; Ids is a list of indices into the td-entry-ar field of td, each of which is
; associated with a clause-list whose set of function symbols is a subset of
; those occurring in the input cl-list.

  (declare (xargs :stobjs td))
  (cond
   ((endp ids) (mv nil td))
   (t
    (let ((entry (td-entry-ari (car ids) td)))
      (cond
       ((eq (clause-set-subsumes init-subsumes-count
                                 (access td-entry entry :clause-list)
                                 cl-list)
            t)

; We return the :root and the td, but we may update the td first if subsumption
; also goes the other way.  In that case we may add another entry to the
; :alt-alist before returning.

        (let ((td (if (and (not (eq fn-book *td-book-failed*))
                           (equal fns
                                  (access td-entry entry :fns)) ; optimization

; There is no reason for more than the main entry if its :root is built-in.

                           (access td-entry entry :book)

; There is no point for having two entries with the same book, so we compare
; fn-book both to the main book and the :alt-alist books.

                           (not (or (hons-equal (access td-entry entry :book)
                                                fn-book)
                                    (rassoc-equal
                                     fn-book
                                     (access td-entry entry :alt-alist))))

; We could check the measure, wf-rel, and mp here.  That additional filter
; would likely be a no-op, however, and the potential speed-up seems
; unnecessary.

                           (clause-set-subsumes init-subsumes-count
                                                cl-list
                                                (access td-entry entry
                                                        :clause-list)))
                      (update-td-entry-ari
                       (car ids)
                       (assert$

; We process built-in functions first, so since we checked that (access
; td-entry entry :book) is non-nil above, the new function must not be
; built-in.

                        fn-book
                        (change td-entry entry
                                :alt-alist
                                (acons fn
                                       fn-book
                                       (access td-entry entry
                                               :alt-alist))))
                       td)
                    td)))
          (mv (access td-entry entry :root) td)))
       (t (td-query-subsumer-1 (cdr ids) init-subsumes-count
                               cl-list fn fn-book fns td)))))))

(defun td-query-subsumer (fns cl-list fn wrld td)

; Return a function whose clause-list, stored in td, subsumes cl-list.  Fns,
; which is used heuristically as a filter, is best given as the set of function
; symbols occurring in cl-list.

; We want to avoid checking the same clause-list repeatedly.  We do so by first
; gathering up into a list without duplicates all of the ids of candidate
; clause-lists, which are those whose sets of functions are subsets of fns.

  (declare (xargs :stobjs td))
  (td-query-subsumer-1 (td-ids-filter-by-subset-of fns fns wrld td nil)
                       nil cl-list fn (td-book fn td) fns td))

; Now we work towards updating td with a new entry, which may subsume old
; entries.

(defun td-add-entry (entry td)

; Insert entry into td.  Reuse an index from the free-list if available, else
; add a new index.  Return (mv id entry), where id is the ID of entry.

; WARNING: This function does not update the fns array by adding the ID of
; entry for each function symbol occurring in the clause-list of entry.  But
; that needs to be done!  See td-replace-subsumed-id-lst.

  (declare (xargs :stobjs td))
  (let ((free-list (free-list td)))
    (cond (free-list (let* ((index (car free-list))
                            (td (update-free-list (cdr free-list) td))
                            (td (update-td-entry-ari index entry td)))
                       (mv index td)))
          (t (let* ((index (next-index td))
                    (new-index (1+ index))
                    (td (if (= new-index (td-entry-ar-length td))
                            (resize-td-entry-ar (* 2 new-index) td)
                          td))
                    (td (update-next-index new-index td))
                    (td (update-td-entry-ari index entry td)))
               (mv index td))))))

(defun maybe-update-fns-length-shifted (wrld td)

; The fns array of td must be sufficiently long to accommodate all logic-mode
; functions.  We ensure that here.

  (declare (xargs :stobjs td))
  (let ((max (max-absolute-event-number wrld)))
    (cond
     ((< max (fns-length-shifted td)) td)
     (t (let* ((new-len (ash (+ (* 2 max)
                                (ash 1 (- *fns-length-shift*)))
                             *fns-length-shift*))
               (td (resize-fns new-len td))
               (td (update-fns-length-shifted (ash new-len
                                                   (- *fns-length-shift*))
                                              td)))
          td)))))

(defun td-ids-filter-by-superset-of-1 (fns wrld td acc)
  (declare (xargs :stobjs td))
  (cond ((endp fns) acc)
        (t (td-ids-filter-by-superset-of-1
            (cdr fns) wrld td
            (intersection$ acc
                           (td-fn-id-list (car fns) wrld td))))))

(defun td-ids-filter-by-superset-of (fns wrld td)

; Return the list of all ids of clause-lists whose functions are supersets of
; fns -- and hence, since fns is assumed non-empty, contain at least one
; function in fns.  The algorithm is to start with the list of such ids for
; (car fns) and then keep intersecting with the list of such ids for each
; successive member of fns.

  (declare (xargs :stobjs td))
  (cond ((null fns) ; impossible?
         nil)
        (t (td-ids-filter-by-superset-of-1 (cdr fns)
                                           wrld
                                           td
                                           (strict-merge-sort-<
                                            (td-fn-id-list (car fns) wrld td))))))

(defun td-query-subsumed-id-lst-1 (ids init-subsumes-count cl-list td acc)
  (declare (xargs :stobjs td))
  (cond ((endp ids) acc)
        (t (td-query-subsumed-id-lst-1
            (cdr ids) init-subsumes-count cl-list td
            (let ((old-cl-list (access td-entry (td-entry-ari (car ids) td)
                                       :clause-list)))
              (cond ((eq (clause-set-subsumes init-subsumes-count
                                              cl-list
                                              old-cl-list)
                         t)
                     (cons (car ids) acc))
                    (t acc)))))))

(defun td-query-subsumed-id-lst (fns cl-list wrld td)

; Return a list of ids whose clause-lists are each subsumed by cl-list.  Fns is
; used heuristically as a filter, by restricting to td entries whose :fns are
; supersets of fns; thus, fns is best given as the set of function symbols
; occurring in cl-list.

; We want to avoid checking the same clause-list repeatedly.  We do so by first
; gathering up into a list without duplicates all of the ids of candidate
; clause-lists, which are those whose sets of functions are supersets of fns.

  (declare (xargs :stobjs td))
  (td-query-subsumed-id-lst-1 (td-ids-filter-by-superset-of fns wrld td)
                              nil cl-list td nil))

(defun td-collect-fns (id-lst td acc)
  (declare (xargs :stobjs td))
  (cond ((endp id-lst)

; It is functionally unnecessary to eliminate duplicates, but it might be the
; efficient thing to do.

         (strict-merge-sort-symbol< acc))
        (t (td-collect-fns (cdr id-lst)
                           td
                           (append (access td-entry
                                           (td-entry-ari (car id-lst) td)
                                           :fns)
                                   acc)))))

(defun td-remove-fns (fns-tail subsumed-id-lst new-id new-fns wrld td)
  (declare (xargs :stobjs td))
  (cond ((endp fns-tail) td)
        (t (let* ((fn (car fns-tail))
                  (index (td-fn-index fn wrld))
                  (alist (fnsi index td))
                  (old-ids (cdr (assoc-eq fn alist)))
                  (new-ids0 (if subsumed-id-lst ; optimization
                                (set-difference-eq old-ids subsumed-id-lst)
                              old-ids))
                  (new-ids (if (member-eq fn new-fns)
                               (cons new-id new-ids0)
                             new-ids0))
                  (td (update-fnsi index
                                   (put-assoc-eq fn new-ids alist)
                                   td)))
             (td-remove-fns (cdr fns-tail) subsumed-id-lst new-id new-fns wrld
                            td)))))

(defun td-remove-ids (id-lst td)
  (declare (xargs :stobjs td))
  (cond ((endp id-lst) td)
        (t (let ((td (update-td-entry-ari (car id-lst) nil td)))
             (td-remove-ids (cdr id-lst) td)))))

(defun td-replace-subsumed-id-lst (subsumed-id-lst new-id new-fns wrld td)

; Each id in subsumed-id-lst is to be subsumed by new-id, which is associated
; with a td-entry record whose :FNS is new-fns.  This involves the following
; updates.

; - Ensure that for each id in subsumed-id-lst, and for each function fn in the
;   :FNS of the entry at that id, id is no longer associated with fn in the fns
;   array, but new-id is.  Our algorithm is (a) to union together all such :FNS
;   and, (b) for each fn in that union, take the set-difference of the
;   associated ids with subsumed-id-lst, and then add new-id if fn is in
;   new-fns.

; - Each id in subsumed-id-lst (c) goes on the free-list.  At that time we (d)
;   reclaim storage by setting the values in td-entry-ar to nil, though this
;   isn't necessary.

  (declare (xargs :stobjs td))
  (let* ((fns (td-collect-fns subsumed-id-lst td new-fns))               ; (a)
         (td (td-remove-fns fns subsumed-id-lst new-id new-fns wrld td)) ; (b)
         (td (update-free-list (append subsumed-id-lst (free-list td))
                               td))               ; (c)
         (td (td-remove-ids subsumed-id-lst td))) ; (d)
    td))

(defun termination-clause-set-for-fn (fn clause-size-limit wrld)

; This is based on ACL2 source function termination-theorem.  We return a
; "normalized" termination clause-list, cl-list, except we return nil if this
; function is not suitable for storing termination clauses in the
; termination-database.  (The caller can observe failure because we never
; expect a normalized termination clause-list to be nil.)

; This function assumes that fn is in logic mode and singly recursive.

  (let* ((names (getpropc fn 'recursivep nil wrld))
         (just (assert$ (and names
                             (eq (car names) fn)
                             (null (cdr names)))
                        (getpropc fn 'justification nil wrld))))
    (cond
     ((assert$ just
               (access justification just :subversive-p))
      nil)
     (t
      (let ((measure-alist (measure-alist? names wrld)))
        (cond
         ((eq (car measure-alist) :FAILED)
          nil)
         (t
          (assert$
           just
           (let* ((mp (access justification just :mp))
                  (rel (access justification just :rel))
                  (bodies (get-unnormalized-bodies names wrld))
                  (ruler-extenders-lst (ruler-extenders-lst names wrld))
                  (clause-set
                   (td-cl-lst names bodies ruler-extenders-lst
                              measure-alist mp rel clause-size-limit wrld)))
             (cond
              ((eq clause-set :failed) nil)
              (t clause-set)))))))))))

(defun td-remove-stubs (syms acc)
  (declare (xargs :guard (and (symbol-listp syms)
                              (symbol-listp acc))
                  :mode :logic))
  (cond ((endp syms) acc)
        (t (td-remove-stubs (cdr syms)
                            (cond ((member-eq (car syms) *td-stub-names*) acc)
                                  (t (cons (car syms) acc)))))))

(defun td-query (fn wrld td fns-limit clause-size-limit)

; Warning: This function assumes that maybe-update-fns-length-shifted has been
; run.

; This is a full-blown query in the sense that it can update the database, td,
; as discussed above.

; Fn should be a :logic-mode, singly-recursive function.

  (declare (xargs :stobjs td))
  (let ((cl-list (termination-clause-set-for-fn fn clause-size-limit wrld)))
    (cond
     ((null cl-list) ; failure
      (mv nil td))
     (t
      (let ((fns

; By keeping the :fns sorted, we can use a linear-time subset test.  See the
; call of subsetp-eq-linear in td-ids-filter-by-subset-of-1.

             (merge-sort-symbol<
              (td-remove-stubs
               (all-ffn-symbs-lst-lst cl-list nil)
               nil))))
        (cond
         ((and fns-limit
               (> (length fns) fns-limit))
          (mv nil td))
         (t
          (mv-let (fn2 td)
            (td-query-subsumer fns cl-list fn wrld td)
            (cond
             (fn2 (mv fn2 td))
             (t
              (let ((book (td-book fn td)))
                (if (eq book *td-book-failed*)
                    (mv nil td)
                  (mv-let (id td)
                    (td-add-entry (make td-entry
                                        :fns fns
                                        :clause-list cl-list
                                        :root fn
                                        :book book)
                                  td)
                    (let* ((subsumed-id-lst
                            (td-query-subsumed-id-lst fns cl-list wrld td))
                           (td (td-replace-subsumed-id-lst subsumed-id-lst
                                                           id fns wrld td)))
                      (mv nil td)))))))))))))))

(defun td-init-fn-1 (fns wrld td fns-limit clause-size-limit)
  (declare (xargs :stobjs td))
  (cond ((endp fns) td)
        (t (let ((prop (getpropc (car fns) 'recursivep nil wrld)))
             (cond ((and prop
                         (null (cdr prop)))
                    (mv-let (fn td)
                      (td-query (car fns) wrld td fns-limit clause-size-limit)
                      (declare (ignore fn))
                      (td-init-fn-1
                       (cdr fns) wrld td fns-limit clause-size-limit)))
                   (t (td-init-fn-1
                       (cdr fns) wrld td fns-limit clause-size-limit)))))))

(defun td-init-fn (world system-books-dir td fns-limit clause-size-limit)

; World is an installed world.  It needs to be the variable, world, since we
; call function-theory below.

  (declare (xargs :stobjs td))
  (let* ((td (td-reset td))
         (td (maybe-update-fns-length-shifted world td))
         (td (update-book-alist (make-fast-alist
                                 (td-book-alist (reverse world)
                                                nil system-books-dir nil))
                                td))
         (old-fns (strip-cadrs

; We reverse the function-theory so that every subsumption equivalence class
; that contains a built-in will have a built-in :root.x

                   (reverse
                    (function-theory :here)))))
    (td-init-fn-1 old-fns world td fns-limit clause-size-limit)))

(defmacro td-init (&key fns-limit clause-size-limit)
  `(time$ (td-init-fn (w state)
                      (f-get-global 'system-books-dir state)
                      td ,fns-limit ,clause-size-limit)))

(defun write-td-cands (n td wrld acc)
  (declare (xargs :stobjs (td)))
  (cond
   ((zp n) acc)
   (t
    (let* ((n (1-f n))
           (entry (td-entry-ari n td)))
      (write-td-cands
       n td wrld
       (cond
        ((null entry) acc)
        (t (cons
            (let* ((aa (access td-entry entry :alt-alist))
                   (root (access td-entry entry :root))
                   (just (getpropc root 'justification nil wrld))
                   (clause-list (access td-entry entry :clause-list))
                   (roots-alist (cons (make roots-alist-entry
                                            :root root
                                            :arity (length (formals root wrld))
                                            :book (access td-entry entry :book))
                                       aa)))
              (make td-candidate
                    :justification just
                    :clause-list clause-list
                    :roots-alist roots-alist))
            acc))))))))

(defun write-td-fn-include-books-extra (chan state)

; After (include-book "doc/top" :dir :system), in raw Lisp, we find the
; packages that are present but whose book is "doc/top" (here, <ACL2> denotes
; the path to the top-level ACL2 directory):

;   (value :q)
;   (let ((doc-top-book
;          (concatenate 'string
;                       (f-get-global 'system-books-dir *the-live-state*)
;                       "doc/top.lisp")))
;     (loop for x in (known-package-alist *the-live-state*)
;           when (equal (car (package-entry-book-path x))
;                       doc-top-book)
;           collect (car x)))

  (declare (xargs :stobjs state))
  (princ$ "
; \"MEMOIZE\"
(include-book \"centaur/memoize/portcullis\" :dir :system)
; \"MILAWA\" -- omitted because of trust tag
; (include-book \"projects/milawa/ACL2/portcullis\" :dir :system))
; \"REWRITE-CODE\"
(include-book \"hacking/rewrite-code\" :dir :system)
; \"ACL2-HACKER\"
(include-book \"hacking/hacker\" :dir :system)
; \"ABNF\"
(include-book \"kestrel/abnf/portcullis\" :dir :system)
; \"RTL\" -- already included
; \"BED\"
(include-book \"centaur/bed/portcullis\" :dir :system)
; \"SV\" -- already included
" chan state))

(defun pkg-books-1 (pkg-entries system-books-dir)
  (cond ((endp pkg-entries) nil)
        (t
         (let* ((entry (car pkg-entries))
                (full-book-name (car (package-entry-book-path entry)))
                (full-book (and full-book-name ; nil for built-ins
                                (remove-lisp-suffix full-book-name t)))
                (sysfile (and full-book
                              (make-sysfile full-book system-books-dir))))
           (cond ((and sysfile
                       (if (sysfile-p sysfile)
                           (not (equal (sysfile-filename sysfile)
                                       "doc/top"))
                         t))
                  (cons sysfile
                        (pkg-books-1 (cdr pkg-entries) system-books-dir)))
                 (t
                  (pkg-books-1 (cdr pkg-entries) system-books-dir)))))))

(defun pkg-books (state)
  (declare (xargs :stobjs state))
  (remove-duplicates-equal
   (pkg-books-1 (known-package-alist state)
                (f-get-global 'system-books-dir state))))

(defun map-include-book (sysfile-lst acc)
  (cond ((endp sysfile-lst) (reverse acc)) ; reverse is optional
        (t (map-include-book
            (cdr sysfile-lst)
            (cons (let ((x (car sysfile-lst)))
                    (if (sysfile-p x)
                        `(include-book ,(sysfile-filename x) :dir :system)
                      `(include-book ,x)))
                  acc)))))

(defun pkg-include-books (state)
  (declare (xargs :stobjs state))
  (map-include-book (pkg-books state) nil))

(defconst *td-fn-header*
  "; NOTE: This file has been automatically generated.

(in-package \"ACL2\")
")

(defun td-wf-rel-alist (td-candidate-lst td acc)
  (declare (xargs :stobjs td))
  (cond
   ((endp td-candidate-lst) acc)
   (t (td-wf-rel-alist (cdr td-candidate-lst)
                       td
                       (let* ((td-cand (car td-candidate-lst))
                              (just (access td-candidate td-cand
                                            :justification))
                              (rel (access justification just :rel)))
                         (cond ((or (eq rel 'o<)
                                    (hons-get rel acc))
                                acc)
                               (t (let ((sysfile (td-book rel td)))
                                    (hons-acons rel sysfile acc)))))))))

(defun write-td-fn (book-name form td state)
  (declare (xargs :stobjs (td state)))
  (mv-let (erp val state)
    (state-global-let*
     ((fmt-hard-right-margin 100000 set-fmt-hard-right-margin)
      (fmt-soft-right-margin 100000 set-fmt-soft-right-margin))
     (pprogn
; Write book-name.acl2.
      (mv-let (chan state)
        (open-output-channel (concatenate 'string book-name ".acl2")
                             :character
                             state)
        (pprogn (princ$ *td-fn-header* chan state)
                (princ$ "
; The following books are included to provide the packages that are
; defined after including system book \"doc/top\".
"
                        chan state)
                (fms!-lst (pkg-include-books state) chan state)
                (fms "~%; Next we deal with packages whose associated book ~
                      in~%;~ ~ ~ ~x0~%; is community book \"doc/top\", which ~
                      is too large to include efficiently.~%"
                     (list (cons #\0 '(known-package-alist state)))
                     chan state nil)
                (write-td-fn-include-books-extra chan state)
                (close-output-channel chan state)))
; Write book-name.lisp.
      (mv-let (chan state)
        (open-output-channel (concatenate 'string book-name ".lisp")
                             :character state)
        (let* ((wrld (w state))
               (td-candidate-lst (write-td-cands (next-index td) td wrld nil))
               (td-wf-rel-alist (td-wf-rel-alist td-candidate-lst td nil))
               (td-cands-alist
                (td-cands-alist (reverse td-candidate-lst) nil)))
          (pprogn (princ$ *td-fn-header* chan state)
                  (fms! "; This file was written by evaluating the ~
                         form:~%#||~|~X01~|||#~|~%(defconst *td-wf-rel-alist* ~
                         (quote~|~X21))~|~%(defconst *td-candidates* ~
                         (quote~|~X31))~|"
                       (list (cons #\0 form)
                             (cons #\1 nil)
                             (cons #\2 td-wf-rel-alist)
                             (cons #\3 td-cands-alist))
                       chan state nil)
                  (close-output-channel chan state))))
      (value nil)))
    (declare (ignore erp val))
    state))

(defmacro write-td (&whole form
                           book-name
                           &key
                           (fns-limit ':none)
                           clause-size-limit)
  (cond ((not (eq fns-limit :none))
         `(let* ((td (td-init :fns-limit ,fns-limit
                              :clause-size-limit ,clause-size-limit))
                 (state (write-td-fn ,book-name ',form td state)))
            (mv td state)))
        (t `(write-td-fn ,book-name ',form td state))))
