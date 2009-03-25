; Hons Archives
; Copyright (C) 2009 by Centaur Technology 
;
; Contact: Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")
(include-book "tools/bstar" :dir :system)
(include-book "unicode/read-ints" :dir :system)
(include-book "defsort/uniquep" :dir :system)
(local (include-book "unicode/unsigned-byte-listp" :dir :system))
(local (include-book "unicode/signed-byte-listp" :dir :system))
(local (include-book "arithmetic-3/bind-free/top" :dir :system))



;                       FILE PRIMITIVES (BOZO)
;
; BOZO.  Some day, we should consider moving these to the unicode library, and
; also think about the guard verification of the writing functions.

(defund combine24u (x1 x2 x3)
  "Given unsigned bytes x1, x2, x3, compute 
     (x1 << 16) | (x2 << 8) | x3
  and interpret the result as a 24-bit unsigned integer."
  (declare (type (unsigned-byte 8) x1)
           (type (unsigned-byte 8) x2)
           (type (unsigned-byte 8) x3))
  (logior (ash x1 16)
          (ash x2 8)
          x3))

(defthm combine24u-unsigned-byte
  (implies (and (force (unsigned-byte-p 8 x1))
                (force (unsigned-byte-p 8 x2))
                (force (unsigned-byte-p 8 x3)))
           (unsigned-byte-p 24 (combine24u x1 x2 x3)))
  :hints(("Goal" :in-theory (enable combine24u))))

(defun read-24ule (channel state)
  (declare (xargs :guard (and (state-p state)
                              (symbolp channel)
                              (open-input-channel-p channel :byte state))
                  :guard-hints(("Goal" :in-theory (enable combine24u)))
                  :stobjs state))
  (mv-let (x1 state) (read-byte$ channel state)
  (mv-let (x2 state) (read-byte$ channel state)
  (mv-let (x3 state) (read-byte$ channel state)
  (if (null x1)
      (mv nil state)
    (if (or (null x2)
            (null x3))
        (mv 'fail state)
      (mv (mbe :logic (combine24u x3 x2 x1)
               :exec (logior 
                      (the (unsigned-byte 24) 
                        (ash (the (unsigned-byte 8) x3) 16))
                      (the (unsigned-byte 16) 
                        (ash (the (unsigned-byte 8) x2) 8))
                      (the (unsigned-byte 8) 
                        x1)))
          state)))))))

(defun write-24ule (x channel state)
  (declare (xargs :guard (and (natp x)
                              (< x (expt 2 24))
                              (state-p state)
                              (symbolp channel) 
                              (open-output-channel-p channel :byte state))
                  :mode :program ;; guards too hard for now
                  :stobjs state))

; Write a 24-bit quantity to a file as a series of three bytes, in
; little-endian order.  

  (let* ((state (write-byte$ 
                 (the (unsigned-byte 8) 
                   (logand (the (unsigned-byte 32) x)
                           (the (unsigned-byte 8) #xFF)))
                 channel state))
         (state (write-byte$ 
                 (the (unsigned-byte 8) 
                   (logand (the (unsigned-byte 8) 
                             (ash (the (unsigned-byte 32) x) -8))
                           (the (unsigned-byte 8) #xFF)))
                 channel state))
         (state (write-byte$ 
                 (the (unsigned-byte 8) 
                   (logand (the (unsigned-byte 8) 
                             (ash (the (unsigned-byte 32) x) -16))
                           (the (unsigned-byte 8) #xFF)))
                 channel state)))
    state))

(defun write-32ule (x channel state)
  (declare (xargs :guard (and (natp x)
                              (< x (expt 2 32))
                              (state-p state)
                              (symbolp channel) 
                              (open-output-channel-p channel :byte state))
                  :mode :program ;; guards too hard for now
                  :stobjs state))

; Write a 32-bit quantitity to a file as a series of four bytes, in
; little-endian order.

  (let* ((state (write-byte$ 
                 (the (unsigned-byte 8) 
                   (logand (the (unsigned-byte 32) x)
                           (the (unsigned-byte 8) #xFF)))
                 channel state))
         (state (write-byte$ 
                 (the (unsigned-byte 8) 
                   (logand (the (unsigned-byte 8) 
                             (ash (the (unsigned-byte 32) x) -8))
                           (the (unsigned-byte 8) #xFF)))
                 channel state))
         (state (write-byte$ 
                 (the (unsigned-byte 8) 
                   (logand (the (unsigned-byte 8) 
                             (ash (the (unsigned-byte 32) x) -16))
                           (the (unsigned-byte 8) #xFF)))
                 channel state))
         (state (write-byte$ 
                 (the (unsigned-byte 8) 
                   (logand (the (unsigned-byte 8) 
                             (ash (the (unsigned-byte 32) x) -24))
                           (the (unsigned-byte 8) #xFF)))
                 channel state)))
    state))




;                               INTRODUCTION
;
; In this section, we have the documentation, an overview of the algorithm, and
; we also provide basic versions of the compression and decompression routines.
;

(defdoc hons-archive
  ":Doc-Section hons-archive
  Mechanism for serializing ACL2 objects~/

  Hons Archives (HARs) are a way to write ACL2 objects to disk so they can be loaded
  in other ACL2 sessions.

  ACL2 already provides a couple of other ways to do this, for instance ~pl[io]
  for a description of ~c[print-object$] and ~c[read-object].  Users of ACL2h may
  also be interested in ~c[compact-print-file] and ~c[compact-read-file], from
  ~c[hons-raw.lisp].  By comparison, hons archives are typically slower to create
  but faster to load than these other methods.


  Hons archives can be created with the ~c[har-zip] macro,
  ~bv[]
     (har-zip x filename
              :sortp {t, nil})
       -->
     state
  ~ev[]
  This macro implicitly takes ~c[state], so it can only be used in contexts
  where ~c[state] is available, such as the top-level loop, make-events, and so
  on.

  The ~c[filename] is really a prefix, and each hons archive actually consists of
  two files on disk,
  ~bv[]
    - foo.har-atoms, a table of atoms, and
    - foo.har-conses, a list of instructions for building conses,
  ~ev[]
  so to successfully move a hons archive, you will need to move both of these
  files.

  By default, ~c[:sortp] is ~c[nil] and the atoms are written to the file in whatever
   seemingly-random order is produced as we walk over the object.  But if ~c[:sortp] 
  is set to ~c[t], the atoms are instead printed in a sorted order.  This takes 
  additional time and does not give any benefit to unzipping.  However, it may result
  in more useful \"diffs\" between various revisions of the atoms file.


  Hons archives can be read with the ~c[har-unzip] macro,
  ~bv[]
     (har-unzip filename 
                :honsp {t, nil})
       -->
     (mv x state)
  ~ev[]
  Because of the use of state, one typically needs to use ~il[make-event] 
  to actually get at the contents of a HAR, e.g.,
  ~bv[]
    (make-event 
     (mv-let (obj state) (time$ (har-unzip \"big.har\"))
             (value `(defconst *big* ',obj))))
  ~ev[]

  The ~c[:honsp] argument controls whether the object will be reconstructed
  via ~il[cons] or ~il[hons].  By default, ~il[cons] is used because it is the
  faster alternative.  On the other hand, if you need the object to be part of
  the hons frontier, you may wish to set ~c[:honsp t] instead of manually 
  ~il[hons-copy]ing the object afterwards.


  Program Mode Note.  There is nothing \"under the hood\" about these functions
  (beyond the use of hons and fast-alists), and in principle we can introduce 
  them all in logic mode and verify their guards.  I do not have time to do this
  right now, so for now they are in program mode.
  ~/
  ")

(defun har-gather-atoms1 (x n tbl)
  (declare (xargs :guard (natp n)
                  :verify-guards nil))

; X is an object we wish to compress.  We are constructing a fast-alist (tbl)
; which maps every atom in x to a unique index.  N is the next available index,
; and we just count upwards.  This effectively builds the table in "unsorted"
; order.

  (if (atom x)
      (if (hons-get-fn-do-not-hopy x tbl)
          (mv (mbe :logic (nfix n)
                   :exec n)
              tbl)
        (mv (mbe :logic (+ (nfix n) 1) 
                 :exec (+ n 1))
            (hons-acons x 
                        (mbe :logic (nfix n) 
                             :exec n) 
                        tbl)))
    (mv-let (n-prime tbl-prime)
            (har-gather-atoms1 (car x) n tbl)
            (har-gather-atoms1 (cdr x) n-prime tbl-prime))))

(defthm natp-of-car-of-har-gather-atoms1
  (natp (car (har-gather-atoms1 x n tbl))))

(defthm alistp-of-har-gather-atoms1
  (implies (alistp tbl)
           (alistp (mv-nth 1 (har-gather-atoms1 x n tbl)))))

(verify-guards har-gather-atoms1)



(defun har-atom-list-to-index-map (x n acc)
  (declare (xargs :guard (natp n)))

; We build a fast-alist of indices to atoms, given
;   - X, the list of atoms in index order,
;   - N, the current index we are on, and
;   - ACC, the fast-alist we have built so far.

  (if (consp x)
      (har-atom-list-to-index-map (cdr x) 
                                  (+ n 1)
                                  (hons-acons n (car x) acc))
    acc))

(defun har-atom-list-to-atom-map (x n acc)
  (declare (xargs :guard (natp n)))

; We build a fast-alist of atoms to indices, given
;   - X, the list of atoms in index order,
;   - N, the current index we are on, and
;   - ACC, the fast-alist we have built so far.

  (if (consp x)
      (har-atom-list-to-atom-map (cdr x) 
                                 (+ n 1)
                                 (hons-acons (car x) n acc))
    acc))

(defund har-gather-atoms (x sortp)
  (declare (xargs :guard t))
  (mv-let (num-atoms unsorted-alist)
          (har-gather-atoms1 x 0 nil)
    (if (not sortp)
        (mv num-atoms unsorted-alist)
      (b* ((-            (flush-hons-get-hash-table-link unsorted-alist))
           (atoms        (strip-cars unsorted-alist))
           (sorted-atoms (<<-sort atoms))
           (sorted-alist (har-atom-list-to-atom-map sorted-atoms 0 nil)))
          (mv num-atoms sorted-alist)))))





(defun har-gather-conses (x n tbl insts amap)
  (declare (xargs :guard (natp n)
                  ;; BOZO verify guards some day
                  :verify-guards nil))

; X is the object we want to compress.  Ideally, the conses in X should be
; maximally shared, i.e., with hons-copy, but we do not check this or try to
; make the object unique.
;
; We are going to walk through X and assign indices to its every unique cons.
; N is the currently free index which we are starting from, and we just keep
; counting up.
;
; As we walk through, we construct a table which maps the conses in X to their
; indices.  TBL is the table we have constructed so far, and in this routine we
; will add to it.
;
; The indices we assign are disjoint from the indices for the atoms in X.  The
; argument AMAP is the map of atoms to their indices, constructed by
; har-gather-atoms.
;
; Finally, the main contribution of this function is to construct INSTS, which
; is a table of instructions that explain how X can be recreated.  Each
; instruction is a cons of two indices, and we accumulate the instructions in
; reverse order.
;
; How do INSTS work?  To begin with, we have already given every atom an index
; and we can look at these indices with AMAP.  Recursively assume that for any
; cons, we can determine the index of its CAR and its CDR.  Suppose that the
; index of the CAR is 5, and that the index of the CDR is 7.  Then, to
; reconstruct X, we only have to cons together the objects pointed to by
; indexes 5 and 7.  The instruction for X, then, is (CONS 5 7).
;
; We return (MV MY-INDEX NEW-N NEW-TBL NEW-INSTS), where MY-INDEX is the index
; for X, which we have either previously assigned or have just assigned, where
; NEW-N is the next free index after processing X, where NEW-TBL is an updated
; TBL which includes X and all of its children, and where NEW-INSTS are the new
; set of instructions which include how to build X, itself.

  (if (atom x)
      (mv (cdr (hons-get-fn-do-not-hopy x amap)) n tbl insts)
    
    (let ((lookup (hons-get-fn-do-not-hopy x tbl)))
      (if lookup
          (mv (cdr lookup) n tbl insts)
        (b* (((mv car-index n tbl insts) 
              (har-gather-conses (car x) n tbl insts amap))
             ((mv cdr-index n tbl insts)
              (har-gather-conses (cdr x) n tbl insts amap)))
            (mv n 
                (+ n 1)
                (hons-acons x n tbl)
                (cons (cons car-index cdr-index) insts)))))))



(defun har-compress (x sortp)
  (declare (xargs :guard t
                  ;; BOZO verify guards some day
                  :verify-guards nil))

; This is the clearest explanation of the compression process.
;
; X is an object to compress.  
;
; We return (MV NUM-ATOMS MAX-INDEX ALST INSTS), where
;   - NUM-ATOMS is the number of atoms
;   - MAX-INDEX is the total number of indexes
;   - ALST is the list of atoms (in index order)
;   - INSTS are the instructions for building the conses (in reverse order)

  (b* (((mv num-atoms amap)         (har-gather-atoms x sortp))
       ((mv max-index & tbl insts)  (har-gather-conses x num-atoms nil nil amap))
       (alst                        (strip-cars (reverse amap)))
       (-                           (flush-hons-get-hash-table-link amap))
       (-                           (flush-hons-get-hash-table-link tbl)))
      (mv num-atoms max-index alst insts)))


(defun har-decompress1 (instrs map map-size)
  (declare (xargs :guard (equal map-size (len map))
                  ;; BOZO figure out adequate guards and verify them some day.
                  :verify-guards nil))

; We don't actually expect to call this function, but it's the clearest
; explanation of what the decompression process involves, and is free of file
; I/O operations.  Eventually it would eb good to prove the equivalence of this
; and the file reading ops, below.
;
; INSTRS are a list of instructions to process, in the proper order.  Map is a
; mapping of indexes to objects which we have constructed so far.  Map-size is 
; the current size of map and also is the index for this instruction.

  (if (atom instrs)
      map
    (let* ((instr1 (car instrs))
           (sub1   (car instr1))
           (sub2   (cdr instr1))
           (sub1-resolve 
            (cond ((and (natp sub1)
                        (< sub1 map-size))
                   (cdr (hons-get-fn-do-not-hopy sub1 map)))
                  (t
                   (er hard? 'har-decompress-instrs "Illegal index: ~x0.~%" sub1))))
           (sub2-resolve 
            (cond ((and (natp sub2)
                        (< sub2 map-size))
                   (cdr (hons-get-fn-do-not-hopy sub2 map)))
                  (t
                   (er hard? 'har-decompress-instrs "Illegal index: ~x0.~%" sub2))))
           (this
            (hons sub1-resolve sub2-resolve)))
      (har-decompress1 (cdr instrs)
                       (hons-acons map-size this map)
                       (+ 1 map-size)))))

(defun har-decompress (an alst instrs)
  (declare (xargs :guard t
                  ;; BOZO figure out appropriate guards, verify them
                  :verify-guards nil))

; As before we don't expect to call this function in practice, but it explains
; how to do the decompression.
;
; AN is the number of atoms in the atom list, ALST.  INSTRS are the
; instructions for building the conses.  We do the decompression and return X.

  (let ((amap (har-atom-list-to-index-map alst 0 nil)))
    (if (not (= (length amap) an))
        (er hard? 'har-decompress "Atom list is the wrong length.")
      (cdar (har-decompress1 instrs amap an)))))





;                            ZIPPING OBJECTS
;
; We now work towards implementing har-zip.  What data do we need to store
; in files?  We will need
;
;   - The atom list,
;   - The number of atoms,
;   - The maximum index of any cons, and
;   - The instructions
;
; To save the first three objects, we write a list of the form
;
;   (num-atoms max-index . [actual atoms])
;
; into the atoms file.  Then, the instructions are written in a byte-based
; manner into conses file.  The size of each link in this serialized file is
; determined by max-index.  Currently, we support 24-bit and 32-bit links.  If
; we need more objects than that, we will need to add support for larger links.

(defun har-write-instrs24-aux (instrs channel state)
  (declare (xargs :mode :program 
                  :stobjs state))

; Instrs are instructions where the max-index should fit into 24 bits.  The
; channel is a :byte-type output channel.  We write the instructions to the
; channel as a list of 24-bit integers, one after another.

  (if (atom instrs)
      state
    (let* ((state (write-24ule (caar instrs) channel state))
           (state (write-24ule (cdar instrs) channel state)))
      (har-write-instrs24-aux (cdr instrs) channel state))))

(defun har-write-instrs32-aux (instrs channel state)
  (declare (xargs :mode :program 
                  :stobjs state))

; Same as har-write-instrs24-aux, but for 32-bits.

  (if (atom instrs)
      state
    (let* ((state (write-32ule (caar instrs) channel state))
           (state (write-32ule (cdar instrs) channel state)))
      (har-write-instrs32-aux (cdr instrs) channel state))))

(defun har-write-instrs24 (instrs filename state)
  (declare (xargs :mode :program 
                  :stobjs state))

; Instrs are instructions where the max-index should fit into 24 bits.  We
; write them into the file indicated by filename, as 24-bit integers.

  (mv-let (channel state)
          (open-output-channel filename :byte state)
          (if (not channel)
              (prog2$ (er hard? 'har-write-instrs24 "Error opening file ~x0.~%" filename)
                      state)
            (let* ((state (har-write-instrs24-aux instrs channel state))
                   (state (close-output-channel channel state)))
              state))))

(defun har-write-instrs32 (instrs filename state)
  (declare (xargs :mode :program 
                  :stobjs state))

; Same as har-write-instrs24, but for 32-bits.

  (mv-let (channel state)
          (open-output-channel filename :byte state)
          (if (not channel)
              (prog2$ (er hard? 'har-write-instrs32 "Error opening file ~x0.~%" filename)
                      state)
            (let* ((state (har-write-instrs32-aux instrs channel state))
                   (state (close-output-channel channel state)))
              state))))

(defun har-write-instrs (max-index instrs filename state)
  (declare (xargs :mode :program 
                  :stobjs state))

; INSTRS are a list of instructions and MAX-INDEX is their max index.  We
; determine which format to use, then write the instructions to a file in that
; format.

  (cond ((< max-index (expt 2 24))
         (har-write-instrs24 instrs filename state))
        ((< max-index (expt 2 32))
         (har-write-instrs32 instrs filename state))
        (t
         (prog2$ (er hard? 'har-write-instrs "Implement support for >32 bits.~%")
                 state))))

(defun har-write-objects (x channel state)
  (declare (xargs :mode :program :stobjs state))

; We originally printed the entire atoms file using a single call of
; print-object$.  But doing it on an element-by-element basis puts newlines in
; between the objects, which results in more sensible diffs when sortp is true.

  (if (atom x)
      state
    (let ((state (print-object$ (car x) channel state)))
      (har-write-objects (cdr x) channel state))))

(defun har-write-object-file (x filename state)
  (declare (xargs :mode :program :stobjs state))

; This just writes a single object, X, to the file indicated by FILENAME, using
; ACL2's built-in print-object$.  We use this to write the list of atoms and
; the index information.

  (mv-let (channel state)
          (open-output-channel filename :object state)
          (if (not channel)
              (prog2$ (er hard? 'har-write-object-file 
                          "Error opening file ~x0.~%" filename)
                      state)
            (let* ((state (har-write-objects x channel state))
                   (state (close-output-channel channel state)))
              state))))

(defun har-zip-fn (x filename sortp state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((filename-atoms   (concatenate 'string filename "-atoms"))
       (filename-conses  (concatenate 'string filename "-conses"))
       (- (cw "; har-zip: hons-copying data.~%"))
       (x (hons-copy x))
       (- (cw "; har-zip: compiling hons archive.~%"))
       ((mv num-atoms max-index alst instrs) (har-compress x sortp))
       (- (cw "; har-zip: writing atoms file.~%"))
       (state (har-write-object-file (list* num-atoms max-index alst) filename-atoms state))
       (- (cw "; har-zip: writing conses file.~%"))
       (state (har-write-instrs max-index (reverse instrs) filename-conses state)))
      state))

(defmacro har-zip (x filename &key sortp)
  "See :doc hons-archive"
  `(har-zip-fn ,x ,filename ,sortp state))



;                             UNZIPPING OBJECTS
;
; This is quite similar.  We intertwine our file reading with the creation of 
; the index/object mapping.
;
; In har-decompress1, we just used a fast alist to map indices to reconstructed
; objects.  I originally implemented the unzipping functions below using this
; same approach.  But better performance can be obtained by using an array
; instead of a fast alist.
;
; There are some size limitations in ACL2 arrays, in particular we are limited 
; to (2^28)-1 elements when we call resize.  So, we actually adopt a hybrid 
; approach, where up to the maximum array size of elements are stored in the
; array, and any indices beyond that are stored in a fast alist.  
;
; In practice, the array is usually going to be big enough to store all of the
; elements we want.  For our main test file, the introduction of this stobj has
; decreased the time it takes to read the instructions as follows:
;
;                    fast-alists        har$
;    honsp t         60.5s, 2.6 GB      42.4s, 1.3 GB
;    honsp nil       30.7s, 1.6 GB       5.0s, 323 MB
;
; So that's a pretty good savings.

(defconst *har-max-array-size* 
  ;; This is the maximum size of an array to allocate when we create the local
  ;; stobj for har.  We only create one this big if necessary.  ACL2 limits us 
  ;; to 2^28-1 entries.
  (1- (expt 2 28)))

(defstobj har$
  ;; We use this array to store up to the first *har-max-array-size* entries.
  ;; We use local stobjs, so the size of 1 is irrelevant here.
  (har$-data :type (array t (1)) :resizable t)
  ;; We use this fast alist to store any remaining entries.
  (har$-fal :type t :initially nil)
  :inline t)

(defmacro har$-get (index har len)

; Made into a macro for inlining.  As a function, its guards was:
;
;  (declare (xargs :stobjs har$
;                  :guard (and (natp index)
;                              (equal len (har$-data-length har$)))))

  `(if (< ,index ,len)
       (har$-datai ,index ,har)
     (cdr (hons-get-fn-do-not-hopy ,index (har$-fal ,har)))))

(defmacro har$-set (index val har len)

; Made into a macro for inlining.  As a function, its guards was:
;
;  (declare (xargs :stobjs har$
;                  :guard (and (natp index)
;                              (equal len (har$-data-length har$)))))

  `(if (< ,index ,len)
      (update-har$-datai ,index ,val ,har)
    (update-har$-fal (hons-acons ,index ,val (har$-fal ,har)) ,har)))

(defun har$-load-atom-list (x n har$ len)
  (declare (xargs :stobjs har$
                  :guard (and (natp n)
                              (equal len (har$-data-length har$)))))
  (if (atom x)
      har$
    (let* ((val (car x))
           (har$ (har$-set n val har$ len)))
      (har$-load-atom-list (cdr x) (+ 1 n) har$ len))))

(defun har-read-insts24 (honsp curr-max channel state har$ hlen)
  (declare (xargs :mode :program
                  :verify-guards nil
                  :stobjs (har$ state)))

; Inputs.
;   - Channel points to an instructions file encoded as 24-bit integers.  
;   - State is the ACL2 state.
;   - Honsp says whether to use "hons" or "cons" when rebuilding the object
;   - Curr-max is the maximum index for which we have reconstructed an object
;   - har$ and hlen are the har$ structure and the length of its data.
;
; We return (MV HAR$ STATE), the updated structures.

  (mv-let (sub1 state)
          (read-24ule channel state)
          (if (not sub1)
              ;; Proper termination, just out of instructions.
              (mv har$ state)
            (b* (((mv sub2 state)   
                  (read-24ule channel state))
                 (sub1-resolve 
                  ;; Basic sanity check
                  (cond ((and (integerp sub1)
                              (< (the (unsigned-byte 24) sub1)
                                 (the integer curr-max)))
                         (har$-get sub1 har$ hlen))
                        (t
                         (er hard? 'har-read-insts24 "Illegal index ~x0.~%" sub1))))
                 (sub2-resolve 
                  ;; Basic sanity check
                  (cond ((and (integerp sub2)
                              (< (the (unsigned-byte 24) sub2)
                                 (the integer curr-max)))
                         (har$-get sub2 har$ hlen))
                        (t
                         (er hard? 'har-read-insts24 "Illegal index ~x0.~%" sub2))))
                 (this (if honsp
                           (hons sub1-resolve sub2-resolve)
                         (cons sub1-resolve sub2-resolve)))
                 (har$ (har$-set curr-max this har$ hlen)))
                (har-read-insts24 honsp (+ 1 curr-max) channel state har$ hlen)))))

(defun har-read-insts32 (honsp curr-max channel state har$ hlen)
  (declare (xargs :mode :program
                  :verify-guards nil
                  :stobjs (har$ state)))

; Same as har-read-insts24, but for 32-bit files.

  (mv-let (sub1 state)
          (read-32ule channel state)
          (if (not sub1)
              ;; Proper termination, just out of instructions.
              (mv har$ state)
            (b* (((mv sub2 state)   
                  (read-32ule channel state))
                 (sub1-resolve 
                  ;; Basic sanity check
                  (cond ((and (integerp sub1)
                              (< (the (unsigned-byte 32) sub1)
                                 (the integer curr-max)))
                         (har$-get sub1 har$ hlen))
                        (t
                         (er hard? 'har-read-insts24 "Illegal index ~x0.~%" sub1))))
                 (sub2-resolve 
                  ;; Basic sanity check
                  (cond ((and (integerp sub2)
                              (< (the (unsigned-byte 32) sub2)
                                 (the integer curr-max)))
                         (har$-get sub2 har$ hlen))
                        (t
                         (er hard? 'har-read-insts24 "Illegal index ~x0.~%" sub2))))
                 (this (if honsp
                           (hons sub1-resolve sub2-resolve)
                         (cons sub1-resolve sub2-resolve)))
                 (har$ (har$-set curr-max this har$ hlen)))
                (har-read-insts32 honsp (+ 1 curr-max) channel state har$ hlen)))))

(defun har-read-instrs (honsp num-atoms max-index atom-lst filename state)
  (declare (xargs :mode :program 
                  :stobjs state))
  (mv-let (channel state)
          (open-input-channel filename :byte state)
          (if (not channel)
              (mv (er hard? 'har-read-instrs "Unable to open ~x0.~%" filename)
                  state)
            (b* ((arrsize            
                  (max 1 (min max-index *har-max-array-size*)))
                 ((mv result state)
                  (with-local-stobj 
                   har$
                   (mv-let (result state har$)
                           (b* ((- (cw "; har-read-instrs: allocating ~x0-element array for ~x1 indices.~%"
                                       arrsize max-index))
                                (har$ (resize-har$-data arrsize har$))
                                (har$ (har$-load-atom-list atom-lst 0 har$ max-index))
                                ((mv har$ state)
                                 (cond ((< max-index (expt 2 24))
                                        (har-read-insts24 honsp num-atoms channel state har$ max-index))
                                       ((< max-index (expt 2 32))
                                        (har-read-insts32 honsp num-atoms channel state har$ max-index))
                                       (t
                                        (let ((state (close-input-channel channel state)))
                                          (prog2$ (er hard? 'har-read-instrs "Implement support for >32 bits.~%")
                                                  (mv har$ state))))))
                                (result  (har$-get max-index har$ max-index)))
                               (mv result state har$))
                           (mv result state))))
                 (state (close-input-channel channel state)))
                (mv result state)))))
                 
(defun har-read-objects (channel state acc)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (eofp obj state)
          (read-object channel state)
          (if eofp
              (mv (reverse acc) state)
            (har-read-objects channel state (cons obj acc)))))

(defun har-read-object-file (filename state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (channel state)
          (open-input-channel filename :object state)
          (if (not channel)
              (mv (er hard? 'har-read-object-file "Error opening file ~x0.~%" filename)
                  state)
            (b* (((mv objs state) (har-read-objects channel state nil))
                 (state           (close-input-channel channel state)))
                (mv objs state)))))

(defun har-unzip-fn (honsp filename state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((filename-atoms   (concatenate 'string filename "-atoms"))
       (filename-conses  (concatenate 'string filename "-conses"))
       (-                (cw "; har-unzip: reading ~s0.~%" filename-atoms))
       ;; The atoms file only contains atoms, so there's no reason to bother
       ;; using hons to read it.  So, we temporarily change to hons-read-p nil
       ;; while reading the atoms.  This seems to save about 20% of the time
       ;; when reading our main test file, (17.8 seconds instead of 23.1
       ;; seconds, and 1.2 GB allocated instead of 1.4 GB.)
       (hons-read-p      (f-get-global 'hons-read-p state))
       (state            (f-put-global 'hons-read-p nil state))
       ((mv atoms state) (har-read-object-file filename-atoms state))
       (state            (f-put-global 'hons-read-p hons-read-p state)))
      (if (not (and (consp atoms)
                    (consp (cdr atoms))
                    (= (car atoms) (length (cddr atoms)))))
          (prog2$
           (er hard? 'har-unzip "Atoms file ~s0 is corrupt.~%" filename-atoms)
           (mv nil state))
        (b* ((num-atoms         (first atoms))
             (max-index         (second atoms))
             (alst              (cddr atoms))
             (-                 (cw "; har-unzip: reading ~s0.~%" filename-conses)))
            (har-read-instrs honsp num-atoms max-index alst
                             filename-conses state)))))


(defmacro har-unzip (filename &key honsp)
  "See :doc hons-archive"
  `(har-unzip-fn ',honsp ,filename state)) 


