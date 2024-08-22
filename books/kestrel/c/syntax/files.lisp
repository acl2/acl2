; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "file-paths")

(include-book "kestrel/fty/byte-list" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ files
  :parents (concrete-syntax)
  :short "A simple model and representation of files."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar in @(see grammar) represents the required structure
     of the content of a translation unit,
     which corresponds to the content of a file
     after it has been subjected to preprocessing
     (which may add content from @('#include')d headers).
     Recall that for now we only represent C code after preprocessing,
     so the correspondence between translation units and file contents
     is exact for now (but we will relax this eventually).
     The content of a file can be represented as a list of bytes,
     which must be parsed into a translation unit.")
   (xdoc::p
    "Often a C program, or a C library, or other meaningful C code component,
     consists of multiple translation units, more in general multiple files,
     which in the future will include both headers and source files.
     So here we introduce a notion of a file set as a collection of files,
     purported to contain, together,
     a C program, or C library, or other meaningful C component."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod filedata
  :short "Fixtype of file data."
  :long
  (xdoc::topstring
   (xdoc::p
    "This represents the raw content of a file,
     as a list (i.e. finite sequence) of bytes.
     We wrap that into this fixtype for separation and extensibility."))
  ((unwrap byte-list))
  :pred filedatap)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap filepath-filedata-map
  :short "Fixtype of omaps from file paths to file data."
  :key-type filepath
  :val-type filedata
  :pred filepath-filedata-mapp
  ///

  (defrule filepath-setp-of-keys-when-filepath-filedata-mapp
    (implies (filepath-filedata-mapp map)
             (filepath-setp (omap::keys map)))
    :induct t
    :enable omap::keys))

;;;;;;;;;;;;;;;;;;;;

(fty::defprod fileset
  :short "Fixtype of file sets."
  :long
  (xdoc::topstring
   (xdoc::p
    "A file set is a collection of files with unique paths,
     which we therefore represent as a map from file paths to file data.
     This is wrapped into a one-component product fixtype
     for separation and extensibility."))
  ((unwrap filepath-filedata-map))
  :pred filesetp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fileset-paths ((files filesetp))
  :returns (paths filepath-setp)
  :short "Set of file paths in a file set."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the keys of the map from file paths to file data.")
   (xdoc::p
    "It is more concise, and more abstract,
     than extracting the map and then the keys.")
   (xdoc::p
    "Together with @(tsee file-at-path),
     it can be used as an API to inspect a file set."))
  (omap::keys (fileset->unwrap files))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define file-at-path ((path filepathp) (files filesetp))
  :guard (set::in path (fileset-paths files))
  :returns (data filedatap)
  :short "File data at a certain path in a file set."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the value associated to the key (path) in the map,
     which the guard requires to be in the file set.")
   (xdoc::p
    "It is more concise, and more abstract,
     than accessing the map and then looking up the path.")
   (xdoc::p
    "Together with @(tsee fileset-paths),
     it can be used an as API to inspect a file set."))
  (filedata-fix (omap::lookup (filepath-fix path) (fileset->unwrap files)))
  :guard-hints (("Goal" :in-theory (enable omap::assoc-to-in-of-keys
                                           fileset-paths)))
  :hooks (:fix))
