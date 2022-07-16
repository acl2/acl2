#|
 This file is a part of Colleen
 (c) 2016 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(in-package #:org.shirakumo.pathname-utils)

(defun checkdocs (&optional (package *package*))
  "Check that all functions, classes, and variables have docstrings."
  (do-symbols (symb package)
    (when (eql (symbol-package symb) package)
      (when (and (fboundp symb) (not (documentation symb 'function)))
        (warn "No documentation for function ~s." symb))
      (when (and (boundp symb) (not (documentation symb 'variable)))
        (warn "No documentation for variable ~s." symb))
      (when (and (find-class symb NIL) (not (documentation symb 'type)))
        (warn "No documentation for class ~s." symb)))))

(defmacro setdocs (&body pairs)
  "Easily set the documentation."
  `(progn
     ,@(loop for (var doc) in pairs
             collect (destructuring-bind (var &optional (type 'function))
                         (if (listp var) var (list var))
                       `(setf (documentation ',var ',type) ,doc)))))

(setdocs
  ((*wild-component* variable)
   "The proper value to use for a wild pathname component.")

  ((*wild-inferiors-component* variable)
   "The proper value to use for a wild inferiors pathname component.")
  
  ((*wild-file* variable)
   "A pathname that is wild in its file spec (can match any file).")
  
  ((*wild-directory* variable)
   "A pathname that is wild in its directory spec (can match any directory).")
  
  ((*wild-inferiors* variable)
   "A pathname that has wild inferiors (can match any number of subdirectories).")
  
  ((*wild-path* variable)
   "A pathname that is wild in both its file and its directory.")
  
  (clean-directory-spec
   "Removes superfluous components from the directory spec.

Specifically, if the encountered part is UNSPECIFIC or the
string \".\", it is omitted. If the part is :BACK, the
preceding component is omitted if possible. If not possible,
an equivalent amount of :UP specs are inserted instead.")
  
  (normalize-directory-spec
   "Attempts to normalize the directory specification into one as specified by CLHS.

Also cleans the directory spec.

See CLEAN-DIRECTORY-SPEC.")
  
  (normalize-pathname
   "Returns a normalised form of the given pathname.

More specifically, the given object is ensured to be a pathname
using CL:PATHNAME, then turned into a new pathname with the
following properties: an unspecific component is turned into
NIL and the directory component is normalised through
NORMALIZE-DIRECTORY-SPEC.

See UNSPECIFIC-P
See NORMALIZE-DIRECTORY-SPEC")
  
  (pathname*
   "Ensures that the argument is a pathname.

If a pathname is passed, it is returned verbatim.
If it is anything else, the value is coerced to a pathname using
NORMALIZE-PATHNAME.

See NORMALIZE-PATHNAME")
  
  (unspecific-p
   "Returns true if the given component is unspecific.

This includes :UNSPECIFIC, NIL, and the empty string.")
  
  (relative-p
   "Returns the pathname if it is a relative pathname.

The pathname is coerced using PATHNAME*

See PATHNAME*")
  
  (absolute-p
   "Returns the pathname if it is an absolute pathname.

The pathname is coerced using PATHNAME*

See PATHNAME*")
  
  (logical-p
   "Returns the pathname if it is a logical pathname.

The pathname is coerced using PATHNAME*

See PATHNAME*")
  
  (physical-p
   "Returns the pathname if it is a physical pathname.

The pathname is coerced using PATHNAME*

See PATHNAME*")
  
  (root-p
   "Returns the pathname if it denotes an absolute root directory.

The pathname is coerced using PATHNAME*

See PATHNAME*")
  
  (directory-p
   "Returns the pathname if it denotes a directory (not a file).

The pathname is coerced using PATHNAME*

See PATHNAME*")
  
  (file-p
   "Returns the pathname if it denotes a file (not a directory).

The pathname is coerced using PATHNAME*

See PATHNAME*")
  
  (subpath-p
   "Returns true if SUBPATH denotes a path on a lower level than BASE.

A pathname is considered a subpath of a base pathname if all of
the following are true:
- Their hosts match
- Their devices match
- The base's name is null or their names match
- The base's type is null or their types match
- The directory component of the subpath denotes a subdirectory
  of the directory component of the base.

If the subpath or base are relative pathnames, they are made
absolute by merging them with the root pathname. If the root
pathname is relative, an error is signalled.

The actually returned value is the coerced value of SUBPATH by
NORMALIZE-PATHNAME.

See NORMALIZE-PATHNAME")
  
  (pathname=
   "Returns T if the two pathnames are the same.

Note that this comparison is purely based on the pathnames itself
and does not check whether the two might resolve to the same file
on the system.

Relative pathnames are turned into absolute ones by merging them
with *default-pathname-defaults* before being compared.

Each component of the pathnames are compared using EQUAL, but
treating parts that are UNSPECIFIC-P as the same, regardless
of the way in which they might be unspecific.

If IGNORE-VERSION is non-NIL (the default), then the version
component of the pathnames is not compared. This is useful, as it
can be different for pathnames that appear to be the same on some
implementations.

See UNSPECIFIC-P")

  (pathname-equal
   "Returns T if the two pathnames denote the same file.

Note that this comparison has to access the file system and might
therefore be costly.

First the two pathnames are turned into truenames using TRUENAME
and then compared using PATHNAME=. This should result in a
comparison that returns true in any situation where the two
pathnames really do refer to the same file, but might not look
the same due to symbolic links or similar effects in the file
system.

See CL:TRUENAME
See PATHNAME=")
  
  (to-root
   "Returns the absolute root of the pathname.")
  
  (to-physical
   "Turns the pathname into a physical one if it is not already one.

The pathname is coerced using PATHNAME*

See LOGICAL-P
See CL:TRANSLATE-LOGICAL-PATHNAME
See PATHNAME*")
  
  (to-directory
   "Turns the pathname into a pathname-directory if it is not already one.

If the argument is :UP or :BACK, it is turned into a relative
pathname with the argument as its only pathname-directory-component.
If the argument is :HOME, it is turned into an absolute pathname
pointing to the home directory.
Otherwise the pathname is coerced using PATHNAME*

See PATHNAME*")

  (to-file
   "Turns the pathname into a file pathname.

This means stripping the device, host, and directory components
of the pathname. The given pathname is coerced using PATHNAME*

See PATHNAME*")
  
  (subdirectory
   "Returns a directory-pathname with the given subdirectories appended.

For example, appending \"bar\" and \"baz\" to \"foo/\" will
result in \"foo/bar/baz/\".

The PATHNAME is coerced using TO-DIRECTORY. For any of the
subdirs, if it is a pathname, stream, or keyword, it is coerced
to a pathname using TO-DIRECTORY. If it is a string, it is
coerced using TO-DIRECTORY but with a trailing slash appended.

If you need to preserve the pathname's file component, consider
using DOWNWARDS instead.

See TO-DIRECTORY")
  
  (pop-directory
   "Pops the last component off the pathname-directory part.

The pathname is coerced using PATHNAME*.
Note that this will probably not behave as expected for
pathnames containing :back and :up. For the \"intuitive\"
behaviour to ascend pathnames, see PARENT or UPWARDS.

See PATHNAME*")
  
  (parent
   "Returns the parent of the pathname.

If the pathname is a directory-pathname, it returns a pathname
that points to the parent thereof, if possible. Specifically,
if the directory is relative and empty, :up is inserted. If
it is absolute and empty, the same pathname is returned. If
it is not empty, then the last component of the directory is
removed. If the pathname is a file pathname, this is equivalent
to TO-DIRECTORY.

The pathname is coerced using PATHNAME*.

If you need to preserve the pathname's file component, consider
using UPWARDS instead.

See PATHNAME*
See TO-DIRECTORY")
  
  (upwards
   "Moves the topmost pathname component a level upwards.

Specifically, if we have a file \"foo/bar/baz.jpg\", and move
it upwards by one, the resulting pathname will be 
\"foo/baz.jpg\". If the pathname is a directory-pathname then
the last directory is moved upwards by one.

See PARENT")
  
  (downwards
   "Moves the topmost pathname component a level downwards.

Specifically, if we have a file \"foo/bar.jpg\", and move it
downwards by \"baz\", the resulting pathname will be
\"foo/baz/bar.jpg\". If the pathname is a directory-pathname
then the last directory is moved downwards by one.

See SUBDIRECTORY")
  
  (enough-pathname
   "Like ENOUGH-NAMESTRING but returns an actual pathname.

The pathname is coerced using PATHNAME*

See PATHNAME*")

  (relative-pathname
   "Computes a relative pathname from one place to another.

The pathnames are first turned into absolute ones by 
MERGE-PATHNAMES. Then, the common directory components are
eliminated, leftover directory components on the from path
are converted into :up, and finally the remaining components
of the to path are appended, producing the final directory
component. The name, type, and version are taken from the to
pathname.

If the two pathnames differ in device or host, an error is
signalled instead.

The pathnames are coerced using NORMALIZE-PATHNAME after the
merge.

See NORMALIZE-PATHNAME")

  (file-in
   "Returns a pathname to the given file but in the given directory.

This is useful when carrying over a file to another directory.
Essentially this constructs a pathname with the name and type
of FILE, but the rest of DIR.")
  
  (file-type
   "Returns the actual file type.

This is different from PATHNAME-TYPE in the following manner:
If PATHNAME-TYPE is specific, but contains a dot, only the part
after the dot is used as it would indicate the actual file-type
on any recent system. If PATHNAME-TYPE is unspecific, the
PATHNAME-NAME is specific, and it contains a dot, then that last
part is used instead. Otherwise NIL is returned.")
  
  (file-name
   "Returns the complete file name as it would be used by the OS, if any.")
  
  (directory-name
   "Returns the name of the topmost directory in the pathname, if any.

The pathname is coerced using TO-DIRECTORY

See TO-DIRECTORY")
  
  (directory-separator
   "Returns the namestring separator between directories as a string.")

  (components
   "Returns a plist containing all the components making up the given pathname.

The plist contains the following keys:
  :namestring
  :truename
  :host
  :device
  :name
  :type
  :version
  :directory

If the pathname has no truename, its value in the plist is NIL."))
