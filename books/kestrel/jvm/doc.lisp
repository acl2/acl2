; Documentation for the JVM model
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/defmacrodoc" :dir :system)

(include-book "read-class")

(defxdoc-for-macro read-class
  :parents (axe) ; todo: add a jvm topic
  :short "Read in a .class file and parse and register the class for use by Axe."
  :arg-descriptions
  ((class-file "A path to a .class file, relative to the directory indicated by the @('dir') argument.")
   (dir "Either @('nil'), in which case the @('class-file') is interpreted relative to the @(tsee cbd), or a keyword indicating a directory registered with @(tsee add-include-book-dir) or @(tsee add-include-book-dir!).")))
