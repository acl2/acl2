; Serializing ACL2 Objects
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

(in-package "SERIALIZE")

;; (depends-on "serialize-raw.lsp")

(defdoc serialize
  ":Doc-Section Serialize
  Optimized routines for Serializing ACL2 objects~/

  NOTE: Does not work on GCL.

  We implement some routines for writing arbitrary ACL2 objects to files, and
  for loading those files later.  We usually call these \".sao\" files, which
  stands for (S)erialized (A)CL2 (O)bject.

  User-level commands
  Note: these are macros that implicitly take ~c[state].
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

  Note that ACL2 provides some other mechanisms for doing this, such as 
  ~c[print-object$] and ~c[read-object], and, for hons users, the routines
  ~c[compact-print-file] and ~c[compact-read-file], as well as the book
  ~c[hons-archive/hons-archive] in the system books.  The serialize library 
  has the advantage of producing a single file, and is generally faster than
  other approaches, particularly for very large objects.~/

  We believe serialization is sound and cannot be exploited to \"prove nil.\"
  However, using the serialize library requires accepting a trust tag, due to 
  our use of raw Common Lisp programming.

  The ~c[:verbose] flag can be given to turn on some verbose output that 
  describes what ~c[read] and ~c[write] are doing, including timing data.


  WRITING.

  Writing performance can be particularly bad if the hash tables it uses are
  resized too often.  Because of this, we monitor for these resizes and report
  them.  If you see many messages about tables growing, you should consider 
  increasing the corresponding table size.

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

  These defaults are probably appropriate for \"small\" ACL2 objects, and 
  for large objects you will almost certainly want to increase them.  The
  basic rule to keep in mind is:

    Larger tables = better hashing performance + higher memory allocation

  The memory allocation is basically \"once per call of ~c[write]\", so 
  if you're writing just one big object, make big tables, but if you're 
  writing lots of small objects, keep them small.


  READING.

  The ~c[read] command needs less configuration.

  If the ~c[:honsp] flag is given, then the object returned will be built
  entirely out of honses.  By default, we do not use ~c[hons] because it 
  is slower than ~c[cons].  But using the ~c[:honsp] flag may faster than
  calling ~c[hons-copy] after reading the object.")

(defttag serialize)

(remove-untouchable 'read-acl2-oracle t)

(defun read-fn (filename honsp verbosep state)
  (declare (xargs :guard (and (stringp filename)
                              (booleanp honsp)
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

#-gcl
(ACL2::progn!
 (set-raw-mode t)
 (load
  (compile-file
   (ACL2::extend-pathname (cbd) "serialize-raw.lsp" state))))

