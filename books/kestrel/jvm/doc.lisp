; Documentation for the JVM model
;
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/defmacrodoc" :dir :system)

(include-book "read-class")
(include-book "read-jar")

(defxdoc-for-macro read-class
  :parents (axe-jvm)
  :short "Read in a .class file and parse and register the class for use by Axe."
  :arg-descriptions
  ((class-file "A path to a .class file, relative to the directory indicated by the @('dir') argument.")
   (dir "Either @('nil'), in which case the @('class-file') is interpreted relative to the @(tsee cbd), or a keyword indicating a directory registered with @(tsee add-include-book-dir) or @(tsee add-include-book-dir!).")))

(defxdoc-for-macro read-jar
  :parents (axe-jvm)
  :short "Read in a .jar file and parse and register classes for use by Axe."
  :arg-descriptions
  ((jar-path "A path to a .jar file, relative to the directory indicated by the @('dir') argument.")
   (dir "Either @('nil'), in which case the @('class-file') is interpreted relative to the @(tsee cbd), or a keyword indicating a directory registered with @(tsee add-include-book-dir) or @(tsee add-include-book-dir!).")
   (classes "Classes to read from the .jar.  Either @(':all'), or a list of strings representing class or interface names (usually fully-qualified).  Note that using @(':all') on a large .jar file may cause a huge amount of code to be read in.")
   (verbosep "Whether to print information about the unzipping process.") ; todo: generalize this to cause other kinds of info to be printed
   ))
