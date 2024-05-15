; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/byte-list" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ files
  :parents (concrete-syntax-for-tools)
  :short "A simple model and representation of files."
  :long
  (xdoc::topstring
   (xdoc::p
    "The grammar in @(see grammar) represents the required structure
     of the content of a translation unit,
     which corresponds to the content of a file
     after it has been subjected to preprocessing
     (which may add from from @('#include')d headers).
     Recall that for now we only represent C code after preprocessing,
     so the correspondence between translation units and file contents is exact.
     The content of a file can be represented as a list of bytes,
     which must be parsed into a translation unit.")
   (xdoc::p
    "Often a C program, or a C library, or other meaningful C code component,
     consists of multiple translation units,
     i.e. to multiple files.
     This is even more the case if we consider headers, besides source files,
     as we plan to do in future extensions.
     So here we introduce a notion of a file set as a collection of files,
     purported to contain, together,
     a C program, or C library, or other meaningful C component."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod filepath
  :short "Fixtype of file paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we formalize a file path as anything,
     which we wrap to keep things more abstract and separate.
     In the future we may refine this type with more structure.
     But note that, for instance,
     we could already use strings with slashes and such as file paths."))
  ((unwrap any))
  :pred filepathp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
  :pred filepath-filedata-mapp)

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
