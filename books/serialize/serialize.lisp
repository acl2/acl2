; Serializing ACL2 Objects
; Copyright (C) 2009-2010 Centaur Technology
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

(in-package "SERIALIZE")

;; (depends-on "serialize-raw.lsp")

(defdoc serialize
  ":Doc-Section Serialize
  Optimized routines for Serializing ACL2 objects~/

  NOTE: Does not work on GCL.

  We implement some routines for writing arbitrary ACL2 objects to
  files, and for loading those files later.  We usually call these
  \".sao\" files, which stands for (S)erialized (A)CL2 (O)bject.

  Note that ACL2 provides some other mechanisms for doing this, such as
  ~c[print-object$] and ~c[read-object], and, for hons users, the
  routines ~c[compact-print-file] and ~c[compact-read-file], as well as
  the book ~c[hons-archive/hons-archive] in the system books.  The
  serialize library has the advantage of producing a single file, and is
  generally faster than other approaches, particularly for very large
  objects.~/


  OVERVIEW OF USER-LEVEL COMMANDS.

  We believe the ~c[read] and ~c[write] routines above are sound and
  cannot be exploited to \"prove nil.\" However, using the serialize
  library requires accepting a trust tag, due to our use of raw Common
  Lisp programming.

  To include the serialize book,
  ~bv[]
     (include-book \"serialize/serialize\" :dir :system :ttags (:serialize))
  ~ev[]
  Reading and writing objects can then be done with the following
  macros.  Note that these macros both implicitly take state!
  ~bv[]
    (SERIALIZE::write filename object
                      [:verbose t/nil]
                      [:symbol-table-size <size>]
                      [:number-table-size <size>]
                      [:string-table-size <size>]
                      [:cons-table-size <size>]
                      [:package-table-size <size>])
       --> state

    (SERIALIZE::read filename
                     [:honsp t/nil]
                     [:verbose t/nil])
       --> (mv obj state)
  ~ev[]

  The ~c[:verbose] flag can be given to turn on some verbose output that
  describes what ~c[read] and ~c[write] are doing, including timing
  data.

  The other options are described in more detail below.


  WRITING.

  Writing performance can be particularly bad if the hash tables it uses
  are resized too often.  Because of this, we monitor for these resizes
  and report them.  If you see many messages about tables growing, you
  should consider increasing the corresponding table size.  We have also
  found that sometimes our monitor is inadequate.  So, if you are finding
  bad performance when using ~c[write], increasing the table sizes is a
  highly-recommended first step.

  The sizes you can configure and their defaults are shown below.

  ~bv[]
     Parameter               Default Value
    ----------------------------------------
     :symbol-table-size      32,768  (2^15)
     :number-table-size      32,768  (2^15)
     :string-table-size      32,768  (2^15)
     :cons-table-size        131,072 (2^17)
     :package-table-size     128     (2^7)
    ----------------------------------------
  ~ev[]

  These defaults are probably appropriate for \"small\" ACL2 objects,
  and for large objects you will almost certainly want to increase them.
  The basic rule to keep in mind is:

    Larger tables = better hashing performance + higher memory allocation

  The memory allocation is basically \"once per call of ~c[write]\", so
  if you're writing just one big object, make big tables, but if you're
  writing lots of small objects, keep them small.


  READING.

  The ~c[read] command needs less configuration.

  If ~c[:honsp] is given ~c[t], then the object returned will be built
  entirely out of honses.  By default, we do not use ~c[hons] because it
  is slower than ~c[cons].  But using the ~c[:honsp] flag may faster
  than calling ~c[hons-copy] after reading the object.

  CCL Only.  As an advanced and obscure option, ~c[:honsp] may also be
  given the value ~c[:static], in which case static conses will be
  created with ~c[ccl:static-cons].  These conses are NOT ~c[hons]es,
  but are not moved by CCL's garbage collector, which may have
  applications in certain raw Lisp code.  In any Lisp besides CCL,
  ~c[:static] is treated as ~c[nil].


  NOTES ABOUT BOOKS.

  The serialize library was developed in order to allow very large ACL2
  objects to be loaded into books.  Ordinarily this is carried out using
  ~c[read] within a ~c[make-event], e.g.,

  ~bv[]
  (make-event (mv-let (obj state)
                      (SERIALIZE::read \"my-file\")
                      (value `(defconst *my-file* ',obj))))
  ~ev[]

  However, this scheme is not particularly efficient.

  (Some of the comments below may only be applicable to versions of ACL2
  which include the HONS extension.)

  During ~il[certify-book], the actual call of ~c[SERIALIZE::read] is
  carried out, and this is typically pretty fast.  But then a number of
  possibly inefficient things occur.

    - The ACL2 function ~c[bad-lisp-object] is run on the *my-file*.
      This is memoized for efficiency, but may still take considerable
      time when *my-file* is very large.

    - The checksum of *my-file* is computed.  This is also memoized, but
      as before may still take some time.

    - The expanded *my-file* form is written to book.cert, essentially
      in ~c[compact-print-file] format, creating a very large .cert
      file.

  Then, during ~il[include-book], the ~c[make-event] expansion of is
  loaded, which entirely bypasses the call of ~c[SERIALIZE::read] and
  effectively gives you the performance of compact-read.

  Generally, the serialize library is still a win, since all of these
  inefficiencies exist regardless of how you read the contents of the
  file.  But the moral of the story is that using serialize will only
  help your ~c[certify-book] time, and it only impacts a portion of the
  overall time.

  To avoid this overhead, we have developed a POTENTIALLY UNSOUND
  alternative to SERIALIZE::read, which is available only by loading
  an additional book.  So, if the above scheme is not performing well
  for you, you may wish to ~pl[SERIALIZE::unsound-read].
  ")

(defdoc unsound-read

; We document this here, rather than in the unsound-read book, so that the user
; who merely includes "serialize/serialize" can see all of the documentation.

  ":Doc-Section Serialize
  Unsound alternative to SERIALIZE::read~/

  Note: you should ~pl[SERIALIZE::serialize], \"Notes about books\",
  before reading this topic.

  As its name suggests, ~c[unsound-read] is known to be unsound and you may
  easily use it to prove ~c[nil].  See below for details.  Because of this, it
  is not included in the ordinary serialize book, but is instead only available
  by additionally including the ~c[serialize/unsound-read] book, e.g.,
  ~bv[]
    (include-book \"serialize/unsound-read\" :dir :system :ttags (:unsound-read))
  ~ev[]
  and accepting the ~c[:unsound-read] trust tag.

  To avoid the use of ~c[make-event] when reading files, and by doing so to
  avoid the overhead of all these checks, writing to .cert files, and so on, we
  introduce a new macro, ~c[unsound-read], which is just like ~c[read] except
  that it does not take ~c[state].

  Because it does not take state, ~c[unsound-read] may be used in ordinary
  ~il[defconst] commands, whereas ordinary ~c[read] may only be used in
  ~il[make-events] or other contexts where the ~c[state] is available.  The
  interface is just like ~c[read], except that it does not return ~c[state].
  That is,
  ~bv[]
    (SERIALIZE::unsound-read filename
                             [:honsp t/nil]
                             [:verbose t/nil])
      -->
    obj
  ~ev[] ~/


  EXPLANATION OF UNSOUNDNESS.

  The problem with ~c[unsound-read] is that, since it is a function, it is
  expected to satisfy the functional equality axiom schema, namely,
  ~bv[]
    (equal (SERIALIZE::unsound-read filename honsp verbosep)
           (SERIALIZE::unsound-read filename honsp verbosep))
  ~ev[]
  But we can violate this property by modifying the file system between
  calls of ~c[unsound-read], and the dependence of ~c[unsound-read] upon
  the state is nowhere evident.  For instance, here is a proof of nil that
  is carried out in ~c[serialize/serialize-tests.lisp] by exploiting this
  fact.

  ~bv[]
  (local
   (encapsulate
    ()
    ;; Write NIL to test.sao
    (make-event
     (let ((state (serialize::write \"test.sao\" nil)))
       (value '(value-triple :invisible))))

    ;; Prove that test.sao contains NIL.
    (defthm lemma-1
      (equal (serialize::unsound-read \"test.sao\") nil)
      :rule-classes nil)

    ;; Write T to test.sao
    (make-event
     (let ((state (serialize::write \"test.sao\" t)))
       (value '(value-triple :invisible))))

    ;; Prove that test.sao contains T.
    (defthm lemma-2
      (equal (serialize::unsound-read \"test.sao\") t)
      :rule-classes nil)

    ;; Arrive at our contradiction.
    (defthm qed
      nil
      :rule-classes nil
      :hints((\"Goal\"
              :use ((:instance lemma-1)
                    (:instance lemma-2))
              :in-theory (disable (serialize::unsound-read-fn)))))))
  ~ev[]

  In short, anyone who wishes to use ~c[unsound-read] does so at their peril,
  and must be able to justify to themselves that nobody has changed the files
  out from under them.")

(defttag :serialize)

(remove-untouchable 'read-acl2-oracle t)

(defun read-fn (filename honsp verbosep state)
  (declare (xargs :guard (and (stringp filename)
                              (member-eq honsp '(t nil :static))
                              (booleanp verbosep)
                              (state-p state))
                  :stobjs state)
           (ignore filename honsp verbosep))
  (prog2$
   (er hard? 'read-fn "Raw-lisp definition not installed??")
   (mv-let (erp val state)
           (read-acl2-oracle state)
           (declare (ignore erp))
           (mv val state))))

(defun write-fn (filename obj verbosep symbol-table-size number-table-size
                          string-table-size cons-table-size package-table-size
                          state)
  (declare (xargs :guard (and (stringp filename)
                              (booleanp verbosep)
                              (posp symbol-table-size)
                              (posp number-table-size)
                              (posp string-table-size)
                              (posp cons-table-size)
                              (posp package-table-size)
                              (state-p state))
                  :stobjs state)
           (ignore filename obj verbosep symbol-table-size number-table-size
                   string-table-size cons-table-size package-table-size))
  (prog2$
   (er hard? 'write-fn "Raw-lisp definition not installed??")
   (mv-let (erp val state)
           (read-acl2-oracle state)
           (declare (ignore erp val))
           state)))

(push-untouchable 'read-acl2-oracle t)

(defmacro read (filename &key honsp verbosep)
  `(read-fn ,filename ,honsp ,verbosep state))

(defmacro write (filename obj &key
                          verbosep
                          (symbol-table-size '32768)
                          (number-table-size '32768)
                          (string-table-size '32768)
                          (cons-table-size  '131072)
                          (package-table-size '128))
  `(write-fn ,filename ,obj ,verbosep ,symbol-table-size ,number-table-size
             ,string-table-size ,cons-table-size ,package-table-size
             state))

(make-event
; (Matt K., Nov. 2009) We use make-event here because if instead we use the
; backquoted form (without the backquote), but with "(cbd)" replacing ",cbd",
; then (include-book "serialize/serialize" :dir :system) fails from a directory
; other than this directory, for any Lisp such that *suppress-compile* is
; non-nil.  (So before this change, such include-book fails for every lisp
; except CCL, except if ":load-compiled-file nil" is specified).  The reason
; appears to be that cbd isn't bound to this directory during loading of the
; compiled file.)
 (let ((cbd (cbd)))
   `(ACL2::progn!
     (set-raw-mode t)
     (unless (eq (get-global 'ACL2::host-lisp state) :gcl)
       (let ((f (compile-file (ACL2::extend-pathname ,cbd "serialize-raw.lsp" state))))
         (ACL2::load-compiled f))))))
