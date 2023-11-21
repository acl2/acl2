(in-package #:org.shirakumo.filesystem-utils)

(docs:define-docs
  (function runtime-directory
    "Returns the directory the executable was spawned from.")
  
  (function temporary-directory
    "Returns the directory for temporary files.

Note: This makes no guarantee about the \"temporary-ness\" of the
files. They may be cleared out after a reboot, after the lisp process
terminates, or only at the user's discretion. If you crate temporary
files within this directory, you should delete them after they're no
longer needed.

See MAKE-TEMPORARY-FILE")
  
  (function make-temporary-file
    "Create a path to a temporary file.

If you pass NAME, it is up to you to ensure that the path can be
re-used if it exists already. Otherwise, the file is guaranteed to not
exist yet.

The file will always be in the system's temporary directory.

See TEMPORARY-DIRECTORY
See WITH-TEMPORARY-FILE")
  
  (function with-temporary-file
    "Execute BODY with a temporary file pathname bound to PATH.

ARGS are passed on to MAKE-TEMPORARY-FILE.
The file is automatically deleted when BODY exits for any reason.

See MAKE-TEMPORARY-FILE
See ENSURE-DELETED")
  
  (function current-directory
    "Accesses the \"current working directory\".

Note that setting this directory is not multithreading safe, as the
directory is global to the process.

See WITH-CURRENT-DIRECTORY")
  
  (function with-current-directory
    "Execute body while the current working directory is changed.

This guarantees the following invariant: the value of
CURRENT-DIRECTORY is the same before entering BODY as it is after BODY
exits for any reason. the value of CURRENT-DIRECTORY is equivalent to
the passed DIRECTORY when BODY begins execution.

See CURRENT-DIRECTORY")
  
  (function ensure-deleted
    "Deletes the given file if it still exists.

See FILE-EXISTS-P
See DELETE-FILE*")
  
  (function truename*
    "Like TRUENAME but ensures that it works on directory files as well on every implementation.")
  
  (function file-exists-p
    "Returns the truename of the file if it exists.")
  
  (function directory*
    "Lists files matching the wild DIRECTORY pathname.

Like CL:DIRECTORY, but tries *not* to resolve any symlinks of the
listing, returning direct descendants of the directory root.")
  
  (function list-contents
    "Lists all files and directories within DIRECTORY.

See DIRECTORY*")
  
  (function list-files
    "Lists all files within DIRECTORY.

This excludes any subdirectories.
Note that non-regular files are still included in this listing,
meaning that not all returned files are necessarily FILE-P.

See DIRECTORY*
See DIRECTORY-P")
  
  (function list-directories
    "Lists all directories within DIRECTORY.

This excludes any files that don't denote directories, and
specifically returns them as directory pathnames.

See DIRECTORY*
See DIRECTORY-P")
  
  (function list-hosts
    "List all known pathname hosts.

This may return NIL if the implementation cannot enumerate the hosts.")
  
  (function list-devices
    "Lists all known pathname devices.

The HOST may be given as a hint for devices to list under the given
host. The implementation may disregard this hint, however.

This may return NIL if the implementation cannot enumerate the devices.")
  
  (function resolve-symbolic-links
    "Resolve symbolic links in the pathname as much as possible.

This does nothing for paths that are not absolute, physical pathnames.
For absolute, physical pathnames it attempts to resolve all symbolic
links or relative components in the pathname to arrive at a canonical
pathname for the file.")
  
  (function directory-p
    "Returns T if the given pathname points to a directory.

This differs from PATHNAME-UTILS:DIRECTORY-P in the following way:
If the pathname is not a directory pathname and instead points to a
file, but the file is actually a directory file, this function still
returns T.

See PATHNAME-UTILS:DIRECTORY-P")
  
  (function file-p
    "Returns T if the given pathname points to a regular file.

This differs from PATHNAME-UTILS:FILE-P in the following way:
If the pathname is a file pathname, but points to a file that is not a
regular file (and thus a directory, device, symlink, or other type of
file node), then this function returns NIL.

See PATHNAME-UTILS:FILE-P")
  
  (function symbolic-link-p
    "Returns T if the given pathname points to a symbolic link file.

See FILE-P
See DIRECTORY-P
See CREATE-SYMBOLIC-LINK")
  
  (function create-symbolic-link
    "Attempts to create a symbolic link file at LINK-FILE, pointing to DESTINATION-FILE.

This may signal an error for a variety of reasons:
- The filesystem does not support symbolic links
- The implementation does not support creating symbolic links
- The implementation is not permitted to create symbolic links
- The target filesystem cannot be pointed to")
  
  (function rename-file*
    "Renames FILE to TO, overwriting TO if it exists.

Similar RENAME-FILE on most implementations, but ensures the destination
is overwritten if it exists, and does *not* merge the pathname name or
type of the FILE pathname with that of TO. In effect this means it
does what you'd expect, and if TO has no name or type, but FILE does,
they are removed by the rename.")
  
  (function copy-file
    "Copies the file from FILE to TO.

REPLACE may be one of:
  - NIL       Never replaces the destination, and instead skips it.
  - T         Always replaces the destination.
  - :IF-NEWER Only replaces the destination if the source has a more
              recent FILE-WRITE-DATE.

When FILE is a directory, all children are copied to the target. If
SKIP-ROOT is NIL, then the directory-name of FILE is replicated as the
root of all contents within TO. Otherwise, the contents of FILE are
copied directly to TO.")

  (function delete-directory
    "Deletes the given directory.

Will recursively delete files within the directory.
This will *not* follow symbolic links, and instead
delete the link file itself.

See DELETE-FILE*")

  (function delete-file*
    "Deletes the given file.

Will recursively delete files if they are directories.
This will *not* follow symbolic links.

See CL:DELETE-FILE
See DELETE-DIRECTORY
See DIRECTORY-P"))
