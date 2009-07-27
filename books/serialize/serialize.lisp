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
                      [:memconfig <config>]
                      [:verbose t/nil])
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

  The ~c[write] command optionally takes a memory configuration, which is 
  an alist that allows the advanced user to change various hash-table sizes.
  In particular, the valid keys and defaults are as follows.

  ~bv[]
     Parameter               Default Value
    ----------------------------------------
     :symbol-table-size      32,768 (2^15)
     :number-table-size      32,768 (2^15)
     :string-table-size      32,768 (2^15)
     :cons-table-size        131,072 (2^17)
     :package-table-size     128 (2^7)
    ----------------------------------------
  ~ev[]

  Here is an example:
  ~bv[]
  (write \"foo.sao\" '(3 . 4)
         :verbosep t
         :memconfig `((:symbol-table-size . ,(expt 2 20))))
  ~ev[]


  These sizes affect certain hash tables that are used while gathering atoms
  and creating the atom map.  We think these defaults are probably appropriate
  for most \"ordinary\" ACL2 objects.

  If your objects are very large, or contain an inordinate amount of symbols,
  numbers, strings, conses, or whatever, then increasing these sizes may 
  improve your writing performance by reducing hash-table collisions and 
  resizing.

  On the other hand, if you are writing lots of small objects, you may wish to
  lower these numbers to reduce the amount of memory allocated on each call to
  ~c[write].


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

(defun write-fn (filename obj verbosep memconfig state)
  (declare (xargs :guard (and (stringp filename)
                              (booleanp verbosep)
                              (alistp memconfig)
                              (state-p state))
                  :stobjs state)
           (ignore filename obj verbosep memconfig))
  (prog2$
   (er hard? 'write-fn "Raw-lisp definition not installed??")
   (mv-let (erp val state)
           (read-acl2-oracle state)
           (declare (ignore erp val))
           state)))

(push-untouchable 'read-acl2-oracle t)

(defmacro read (filename &key honsp verbosep)
  `(read-fn ,filename ,honsp ,verbosep state))

(defmacro write (filename obj &key verbosep memconfig)
  `(write-fn ,filename ,obj ,verbosep ,memconfig state))

#-gcl
(ACL2::progn!
 (set-raw-mode t)
 (load
  (compile-file
   (ACL2::extend-pathname (cbd) "serialize-raw.lsp" state))))

