; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Thanks to Eric Smith for requesting utilities for reducing include-book
; dependencies.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc include-book-paths
  :parents (kestrel-utilities)
  :short "List paths via @(tsee include-book) down to a given book"
  :long "@({
 General Form:

 (include-book-paths book
                     &key
                     excluded-books ; default nil
                     dir ; default (cbd)
                     verbose ; default t
                     return  ; default *include-book-paths-default-count*
                     )
 })

 <p>where all arguments are evaluated.  The value of the first argument,
 @('book'), evaluates to a string that is interpreted as a book name, where the
 @('\".lisp\"') suffix is optional.  @('Excluded-books') evaluates to a list of
 such strings.  Note that in this context, a book name can be an absolute
 pathname or it can be relative to the directory @('dir'), which by default is
 the @(tsee cbd) but can be any directory name or any legal value of the
 @(':dir') argument for @(tsee include-book), e.g., @(':dir :system').  By
 default some progress messages are printed; use @(':verbose nil') to turn them
 off.  We describe the @(':return') keyword argument later below.</p>

 @({
 Example Form:

 (include-book-paths \"cowles/acl2-asg.lisp\"
                     :dir \"/projects/acl2/acl2/books\"
                     :excluded-books '(\"meta/meta-times-equal\")
                     :verbose nil
                     :return t)
 })

 <h3>Description</h3>

 <p>Evaluation of the form @('(include-book-paths A)') returns an @(see
 error-triple).  In the case of no error, the value is a list consisting of
 maximal paths through the ``immediately included by'' relation, defined below,
 that terminate in the given book name, @('A').  The form
 @('(include-book-paths A :excluded-books (list B1 ... Bn))') produces a
 similar result, except that all paths that contain any @('Bi') are excluded
 from the result.  This supports the motivation for writing this tool, which is
 to reduce the set of books on which a given book depends (via
 @('include-book'), hereditarily).  If you are contemplating the possibility of
 removing dependence on each @('Bi'), then @('(include-book-paths A (list B1
 ... Bn))') will give you remaining paths that cause the current session to
 depend on book @('A').</p>

 <p>By default, the maximum number of paths returned is the value of the
 constant @('*include-book-paths-default-count*'), which is
 @(`*include-book-paths-default-count*`).  If the value of keyword @(':return')
 is a natural number, then this number is used in place of that default.  If
 the number of maximal paths exceeds this number, only the first
 @(`*include-book-paths-default-count*`) are returned; otherwise all such paths
 are returned.  Regardless, the full list of maximal paths is stored in @(see
 state) global variable @('include-book-paths-last').  If the value of keyword
 argument @(':return') is supplied as other than a natural number, then all
 such maximal paths are returned, except that if the value is @('nil'), then no
 paths are returned.</p>

 <h3>Details: the algorithm and the notion of ``immediately included by''</h3>

 <p>The algorithm is based on the binary relation ``A is immediately included
 by B'', defined as follows.  First let us say that ``A is included by B'' (or
 ``B includes A'') if within the book B or its @(see portcullis) @(see
 command)s there is an @(see include-book) of A, which may be @(see local).
 Then A is immediately included by B (or, B immediately includes A) when B
 includes A but there is no book C such that B includes C and C includes A.
 Suppose for example that book B contains the following forms, where also book
 C includes book A.</p>

 @({
 (include-book A)
 (include-book C) ; where C includes A
 })

 <p>This is equivalent to the following &mdash; and they are equivalent from a
 dependency standpoint even if either or both of the include-book forms are
 local.</p>

 @({
 (include-book C) ; where C includes A
 })

 <p>Even though B includes A, nevertheless, since also B includes C which
 includes A, then A is not <i>immediately included</i> by B.  The result of
 @('include-book-paths') will include at least one path from B through C to A,
 but no path for which B is adjacent to A.  Our contention is that
 ``immediately includes'' is the right notion for dependency analysis since
 seeing two paths with B connected to A &mdash; one with B adjacent to A and
 one with B connected to C, which is connected to A &mdash; isn't particularly
 helpful, and is perhaps misleading (given the equivalent displays above).</p>

 <h3>The ``immediately included by'' directed acyclic graph, @('iib-dag')</h3>

 <p>The ``immediately included by'' relation is actually a directed acyclic
 graph, which we call the ``iib-dag''.  The first step in the
 @('include-book-paths') algorithm is to build the iib-dag from the @(see
 certificate)s of all books included in the current ACL2 @(see world) (@(see
 local)ly or not).  You can compute the iib-dag yourself by evaluating the
 form</p>

 @({
 (include-book-dag ctx state)
 })

 <p>where @('ctx') is a @(see context) for error messages and @('state') is the
 ACL2 @(see state), and the result is an @(see error-triple) whose value in the
 non-error case is the current iib-dag.</p>

 <p>The iib-dag is actually cached in the @(see state) global variable
 @('include-book-dag-cache'), whose value is either @('nil') or of the form
 @('(cons include-book-alist-all iib-dag)') where @('iib-dag') is the iib-dag
 computed in a world @('w') for which @('include-book-alist-all') is the value
 of @('(global-val 'include-book-alist-all w)').  Thus, if no @(tsee
 include-book) events have been evaluated or undone since the last time the
 iib-dag was computed, then the iib-dag will simply be looked up in the cache.
 This is an important optimization, since building the iib-dag is probably the
 most time-consuming part of the @('include-book-paths') algorithm.</p>

 <p>Remark.  As noted above, the iib-dag is computed from the @(see
 certificate)s of all of the books included in the session (@(see local)ly or
 not).  A duplicate-free list of all such books can be computed as follows.</p>

 @({
  (remove-duplicates-equal
   (strip-cars (global-val 'include-book-alist-all (w state))))
 })")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Description of Algorithm

; First we describe what we'd like the tool to do.  For example, suppose we
; have these include-book chains:

;   "A" is included by "E".
;   "E" is included by "B" and "C".
;   "B" and "C" are included by "F", which is included in the current session.
;   "A" is included locally by "D".
;   "D" is included locally by "G".
;   "G" is included by "H", which is included in the current session.

; Then we'd like the call

;   (include-book-paths "A")

; to evaluate to this list of paths from top-level included books down to the
; "low-level" book, "A":

;   (("F" "B" "E" "A")
;    ("F" "C" "E" "A")
;    ("H" "G" "D" "A"))

; Moreover, since the intended purpose of this tool is to find ways to reduce
; dependencies when including a book, we'd like to be able to exclude paths
; that go through books that we think we might be able to eliminate from our
; dependencies, to see if that would reduce or eliminate the dependency on a
; given lower-level book.  For the example above, the query

;   (include-book-paths "A" "B" "C")

; would eliminate the paths through "B" and "C", resulting in

;   (("H" "G" "D" "A"))

; -- which would also be produced by:

;   (include-book-paths "A" "E")

; In each case, we are presumably not interested in either of the paths from
; "F" down to "A": in the first case because we are contemplating eliminating
; the dependence on "B" and "C", and in the second case because (instead) we
; are contemplating eliminating the dependence on "E".

; Now turning to the algorithm:

; Initially we create an alist (... (A B1 B2 ... Bk) ...), where each key A is
; is a book name and (B1 B2 ... Bk) enumerates the names of books hereditarily
; included by A, possibly locally.  Note that each book name is a canonical
; absolute pathname.  Then, we create an "include-book-dag" with entries (A B1
; B2 ... Bk) that are syntactically of the form described above, but with the
; following two differences, expressing that this time we represent the
; converse relation and only immediate arcs, respectively:

; (1) A is included by each Bi (possibly locally).

; (2) There is no C such that A is included by C, which is included by Bi
;     (where either or both inclusions amy be local).

; Note that if B includes A and also B includes C which includes A, then B will
; not be among the Bi.  This seems OK for our intended use of this tool, which
; is to help to reduce include-book dependencies.  To see this, suppose that
; book B contains these forms:

;   (include-book A)
;   (include-book C) ; where C includes A

; This is equivalent to the following -- and they are equivalent from a
; dependency standpoint even if either or both of the include-book forms are
; local.

;   (include-book C) ; where C includes A

; When we enumerate paths, we'll see the path from B through C to A; our
; contention is taht seeing the path from B directly to A isn't particularly
; helpful, and is perhaps misleading (given the equivalence above).

; Let's call the initial alist hereditarily-includes-alist, and the second
; alist, include-book-dag.  The second is a fast-alist.

(set-state-ok t)
(program)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; include-book-dag
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun books-included-by (full-book-name ctx state)
  (declare (xargs :mode :program))
  (let ((cert-file-name (convert-book-name-to-cert-name full-book-name t)))
    (er-let* ((alist (post-alist-from-pcert1
                      cert-file-name
                      (msg "Unable to open file ~x0 for input."
                           cert-file-name)
                      ctx
                      state)))
      (value
       (remove-duplicates-equal
        (remove1-equal full-book-name
                       (strip-cars (accumulate-post-alist alist nil))))))))

(defun hereditarily-includes-alist (book-lst ctx state acc)
  (cond ((endp book-lst) (value acc))
        (t (er-let* ((books (books-included-by (car book-lst) ctx state)))
             (hereditarily-includes-alist
              (cdr book-lst)
              ctx
              state
              (acons (car book-lst) books acc))))))

(defun invert-alist-to-fal-1 (vals key acc)

; See invert-alist-to-fal.

  (cond ((endp vals) acc)
        (t (invert-alist-to-fal-1
            (cdr vals)
            key
            (let* ((val (hons-copy (car vals)))
                   (old (hons-get val acc)))
              (hons-acons val
                          (cons key (cdr old))
                          acc))))))

(defun invert-alist-to-fal (alist acc)

; Each entry of alist associates a key k with values vi, so that a typical
; member of alist is of the form (k v1 ... vn).  We return a fast-alist that is
; the inverse; thus, for k and any vi as above we will find an entry of the
; form (vi ... k ...).  We accumulate into acc, a fast alist.  We guarantee
; that all strings in acc, and hence in the result, are normed.

  (cond ((endp alist) (fast-alist-fork acc nil))
        (t (let* ((entry (car alist))
                  (key (hons-copy (car entry)))
                  (vals (cdr entry)))
             (invert-alist-to-fal (cdr alist)
                                  (invert-alist-to-fal-1 vals key acc))))))

(defun immediate-fal-3 (val vals fal)

; See immediate-fal-2.

  (cond ((endp vals) t)
        ((member-equal
          val
          (cdr (hons-get (car vals) ; v, as in comment in immediate-fal-2
                         fal)))
         nil)
        (t (immediate-fal-3 val (cdr vals) fal))))

(defun immediate-fal-2 (vals-tail vals fal)

; Collect all val in the list, vals-tail, such that for no v in vals do we have
; an entry (v ... val ...) in fal.  Such a v is what would disqualify val from
; being an immediate neighbor of key.

  (cond ((endp vals-tail) nil)
        ((immediate-fal-3 (car vals-tail) vals fal)
         (cons (car vals-tail)
               (immediate-fal-2 (cdr vals-tail) vals fal)))
        (t (immediate-fal-2 (cdr vals-tail) vals fal))))

(defun immediate-fal-1 (fal-tail fal acc)
  (cond ((endp fal-tail) (fast-alist-fork acc nil))
        (t (let* ((entry (car fal-tail))
                  (key (car entry))
                  (vals (cdr entry)))
             (immediate-fal-1 (cdr fal-tail)
                              fal
                              (hons-acons
                               key
                               (immediate-fal-2 vals vals fal)
                               acc))))))

(defun immediate-fal (fal)

; Fal is a fast-alist that represents a dag, where an entry (key x1 ... xk)
; indicates an arc from key to each xi.  We return a new fast-alist in which
; key is associated only with those xi such that for no y do we have entries
; (key ... y ...) and (y ... xi).

  (let ((ans (immediate-fal-1 fal fal nil)))
    (prog2$ (fast-alist-free fal)
            ans)))

(make-event

; The value of state global 'include-book-dag-cache is either nil or of the
; form (cons (global-val 'include-book-alist-all (w state)) ans) where
; ans is the cached value.

 (pprogn (f-put-global 'include-book-dag-cache nil state)
         (value '(value-triple nil)))
 :check-expansion t)

(defun include-book-dag (ctx state)
  (let ((include-book-alist-all (global-val 'include-book-alist-all (w state)))
        (cache (f-get-global 'include-book-dag-cache state)))
    (cond
     ((equal include-book-alist-all (car cache))
      (value (cdr cache)))
     (t (let ((book-lst (remove-duplicates-equal
                         (strip-cars include-book-alist-all))))
          (er-let* ((hereditarily-includes-alist
                     (hereditarily-includes-alist book-lst ctx state nil)))
            (let ((result (immediate-fal (invert-alist-to-fal
                                          hereditarily-includes-alist
                                          nil))))
              (pprogn
               (f-put-global 'include-book-dag-cache
                             (cons include-book-alist-all result)
                             state)
               (value result)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; include-book-paths
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun include-book-paths-2 (paths excluded dag new-paths old-paths)
  (cond ((endp paths) (mv new-paths old-paths))
        (t (let* ((p (car paths))
                  (node (car p))
                  (node-lst (set-difference-equal (cdr (hons-get node dag))
                                                  excluded)))
             (mv-let (new-paths old-paths)
               (cond (node-lst (mv (append (pairlis-x2 node-lst p) new-paths)
                                   old-paths))
                     (t (mv new-paths (cons p old-paths))))
               (include-book-paths-2 (cdr paths) excluded dag new-paths
                                     old-paths))))))

(defun include-book-paths-1 (paths excluded dag acc)

; For each path P in the given list of non-empty paths, accumulate into acc the
; list of all paths maximally extending P by paths via neighbors in dag.

  (mv-let (new-paths acc)
    (include-book-paths-2 paths excluded dag nil acc)
    (cond (new-paths (include-book-paths-1 new-paths excluded dag acc))
          (t acc))))

(defun maybe-remove-dot-lisp-suffix (x)
  (declare (type string x))
  (let ((len (length x)))
    (cond ((and (<= 5 len)
                (equal (subseq x (- len 5) len)
                       ".lisp"))
           (subseq x 0 (- len 5)))
          (t x))))

(defun full-book-name-lst (books cbd ctx state)
  (cond ((endp books) nil)
        ((not (stringp (car books)))
         (er hard ctx
             "Not a string: ~x0"
             (car books)))
        (t (mv-let (full-book-name directory-name familiar-name)
             (parse-book-name cbd
                              (maybe-remove-dot-lisp-suffix (car books))
                              ".lisp" ctx state)
             (declare (ignore directory-name familiar-name))
             (cons full-book-name
                   (full-book-name-lst (cdr books) cbd ctx state))))))

(defun include-book-paths-fn (book-name excluded-books verbose return dir state)
  (let ((ctx (cons 'include-book-paths book-name))
        (chan (standard-co state)))
    (er-let* ((dag (include-book-dag ctx state)))
      (pprogn
       (cond (verbose
              (pprogn (princ$ "; Note: completed building include-book-dag."
                              chan state)
                      (newline chan state)))
             (t state))
       (let* ((full-book-name-lst
               (full-book-name-lst (cons book-name excluded-books)
                                   dir ctx state))
              (full-book-name (car full-book-name-lst))
              (excluded-books (cdr full-book-name-lst))
              (seed (list (list full-book-name)))
              (result0 (include-book-paths-1
                        seed
                        excluded-books
                        dag
                        nil))
              (result (if (equal result0 seed)
                          nil
                        result0)))
         (pprogn
          (cond
           (verbose
            (let ((len (length result)))
              (mv-let (col state)
                (fmt1 "; Note: completed computing ~n0 ~
                       include-book-paths~@1.~|"
                      (list (cons #\0 len)
                            (cons #\1 (if (and (natp return)
                                               (> len return))
                                          (msg "~|;       (but printing only ~
                                                the first ~x0)"
                                               return)
                                        "")))
                      0 chan state nil)
                (declare (ignore col))
                state)))
           (t state))
          (f-put-global 'include-book-paths-last result state)
          (value (if return
                     (if (and (natp return)
                              (< return (length result)))
                         (take return result)
                       result)
                   :invisible))))))))

(defconst *include-book-paths-default-count*

; This somewhat arbitrary count is intended to limit printing when there are
; very many paths.

  100)

(defmacro include-book-paths (book-name &key
                                        excluded-books
                                        (verbose 't)
                                        (return 'irrelevant return-p)
                                        (dir 'irrelevant dir-p))
  (let ((return (if return-p
                    return
                  *include-book-paths-default-count*))
        (dir (if dir-p
                 dir
               '(cbd))))
    `(include-book-paths-fn ,book-name ,excluded-books ,verbose ,return ,dir state)))
