#|
 This file is a part of mmap
 (c) 2017 Shirakumo http://tymoon.eu (shinmera@tymoon .eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(in-package #:org.shirakumo.fraf.trial.mmap)

(docs:define-docs
  (type mmap-error
    "Error signalled if the mmap attempt fails for some reason.

Possible reasons include, but are not limited to:
- File not found
- File access denied
- Out of memory
- Out of address space
- Mapping not allowed
- Invalid combination of flags

See MMAP
See CODE
See MESSAGE")

  (function code
    "The OS-specific error code returned for the mmap failure.

See MMAP-ERROR")

  (function message
    "The (hopefully) user-readable error message for the mmap failure.

See MMAP-ERROR")

  (function mmap
    "Map the given path or number of bytes into the address space.

PATH can be either a pathname designator, or NIL. If it is NIL, an anonymous
file is mapped and the MMAP flag list must include the flag :ANONYMOUS.
If it is a path, then the contents of the given file on the file system are
mapped into the address space. The file contents can then be read, written,
or executed depending on the given flags as if normal memory was accessed.
If the file is NIL or its size cannot be automatically determined, you must
pass a valid SIZE. You may optionally pass an OFFSET (in bytes) into the
file from which the mapping begins.

If the map attempt fails, an error of type MMAP-ERROR is signalled.
If the call succeeds, three values are returned:

  PTR  --- A CFFI:FOREIGN-POINTER that points to the start of the place in
           memory where the file contents have been mapped. The contents
           should be placed in increasing address order, unless the flag
           :GROWS-DOWN is active.
  FD   --- An opaque file descriptor. You should not touch this.
  SIZE --- The size of the region of memory that has been mapped in bytes.

All three values need to be passed on to MUNMAP completely unchanged. Any
change could cause severe issues.

The three options OPEN, PROTECTION, and MMAP are lists of flags. Not all of
those flags are portable, some are only allowed on Linux, some only on non-
Windows systems. To indicate support, the flags are marked as EVERY, POSIX
\(non-Windows), LINUX, or WINDOWS.

OPEN
 :READ          --- [EVERY] Opens the file for read access.
 :WRITE         --- [EVERY] Opens the file for write access.
 :CREATE        --- [EVERY] Creates the file if it does not exist yet.
 :ENSURE-CREATE --- [EVERY] Creates the file if it does not exist yet and
                            errors if it does.
 :TRUNCATE      --- [EVERY] Truncates the file and replaces it if it exists.
 :DIRECT        --- [EVERY] Causes system buffers to be bypassed.
 :FILE-SYNC     --- [EVERY] Causes writes to the file to be flushed asap.
 :DATA-SYNC     --- [POSIX] Similar to FILE-SYNC, but uses data integrity
                            semantics rather than file integrity semantics.
 :DONT-CLAIM-TTY--- [POSIX] If the file is a tty and the process does not
                            already have a controlling tty, this file will
                            not become the process' controlling tty.
 :NON-BLOCK     --- [POSIX] Attempt to open the file in non-blocking mode,
                            causing operations on the fd to return asap.
 :NO-FOLLOW     --- [LINUX] Errors if the file is a symlink.
 :ASYNC         --- [LINUX] Enable signal driven IO.
 :DIRECTORY     --- [LINUX] Errors if the file is not a directory.
 :LARGE-FILE    --- [LINUX] Allows opening files with size not representable
                            by a 32 bit unsigned integer.

PROTECTION
 :READ          --- [EVERY] Allows reading from the memory region. The OPEN
                            flag :READ is required for this protection mode.
                            This flag is required on windows.
 :WRITE         --- [EVERY] Allows writing to the memory region.
 :EXEC          --- [EVERY] Allows executing code in the memory region.
 :NONE          --- [POSIX] Prevents accessing the memory region.

MMAP
 :PRIVATE       --- [EVERY] The underlying file is not changed if the memory
                            area is written to. Copy-on-write is employed to
                            ensure separation.
 :SHARED        --- [EVERY] The underlying file is changed if the memory
                            area is written to and the change will be
                            visible to other processes. In this case the
                            OPEN flag :WRITE must be specified.
 :ANONYMOUS     --- [LINUX/WINDOWS] The path should be a number of bytes to
                            map to memory. The memory region is then mapped
                            against an \"anonymous\" file.
 :NO-RESERVE    --- [LINUX] Don't reserve swap for this mapping. If memory
                            runs out, a segfault will be generated instead.
 :LOCKED        --- [LINUX] Locks the region to RAM, preventing it from
                            being swapped out.
 :GROWS-DOWN    --- [LINUX] Causes the memory region to be mapped with a
                            decreasing address, like in a stack.
 :POPULATE      --- [LINUX] Pre-populate the memory region with the file
                            contents, which can help performance.
 :NON-BLOCK     --- [LINUX] Only useful with :POPULATE -- do not perform a
                            read-ahead.

The default values for the flags are:
 :OPEN (:READ) :PROTECTION (:READ) :MMAP (:PRIVATE)

Note that if you are intending to use MPROTECT to change the protection of
the mapped file at a later date, you need to call MMAP with the maximal
combination of protection flags first. If this is not the protection that
you want to start out with, call MPROTECT with the correct combination
immediately after. For instance, if you would like to start with (:READ) and
later want to change it to (:READ :WRITE), call MMAP with (:READ :WRITE),
and immediately after call MPROTECT with (:READ).

See MUNMAP
See WITH-MMAP
See MMAP-ERROR
See http://pubs.opengroup.org/onlinepubs/7908799/xsh/mmap.html
See http://pubs.opengroup.org/onlinepubs/009604499/functions/stat.html
See http://man7.org/linux/man-pages/man2/mmap.2.html
See http://man7.org/linux/man-pages/man2/stat.2.html
See https://docs.microsoft.com/en-us/windows/desktop/api/fileapi/nf-fileapi-createfilew
See https://docs.microsoft.com/en-us/windows/desktop/api/fileapi/nf-fileapi-getfilesize
See https://docs.microsoft.com/en-us/windows/desktop/api/winbase/nf-winbase-createfilemappinga
See https://msdn.microsoft.com/en-us/library/windows/desktop/aa366761(v=vs.85).aspx")

  (function munmap
    "Unmaps the memory region, freeing the address space and its file.

The values passed to this function must be the ones retrieved from a call
to MMAP. Calling MUNMAP with the same values more than once will lead to
undefined consequences and may very well corrupt your system to crash. The
same goes for calling MUNMAP with values not directly returned by MMAP,
calling it with changed values returned by MMAP, or attempting to
dereference the PTR after a call to MUNMAP.

This function returns nothing useful.

This function may signal an MMAP-ERROR in case the operating system notices
a problem.

See MMAP
See MMAP-ERROR
See WITH-MMAP
See http://pubs.opengroup.org/onlinepubs/9699919799/functions/mprotect.html
See http://man7.org/linux/man-pages/man2/mprotect.2.html
See https://msdn.microsoft.com/en-us/library/windows/desktop/aa366882(v=vs.85).aspx
See https://msdn.microsoft.com/en-us/library/windows/desktop/ms724211(v=vs.85).aspx")

  (function msync
    "Causes writes to the mapped file area to be written to disk.

The values passed to this function must be the ones retrieved from a call
to MMAP.

The following flags are supported:

 :SYNC          --- [EVERY] Writing is synchronous. A call to this function 
                            will not return until the data is flushed to
                            disk.
 :ASYNC         --- [EVERY] Writing is asynchronous and a call will return
                            immediately.
 :INVALIDATE    --- [POSIX] Asks to invalidate other mappings of the same
                            file, ensuring the view is synchronised.

This function returns nothing useful.

This function may signal an MMAP-ERROR in case the operating system notices
a problem.

See MMAP
See MMAP-ERROR
See http://pubs.opengroup.org/onlinepubs/000095399/functions/msync.html
See http://man7.org/linux/man-pages/man2/msync.2.html
See https://msdn.microsoft.com/en-us/library/windows/desktop/aa366563(v=vs.85).aspx
See https://docs.microsoft.com/en-us/windows/desktop/api/fileapi/nf-fileapi-flushfilebuffers")

  (function mprotect
    "Changes the access protection of the mapped memory region.

The values passed to this function must be the ones retrieved from a call
to MMAP.

The following protection flags are supported:

 :READ          --- [EVERY] Allows reading from the memory region. The OPEN
                            flag :READ is required for this protection mode.
                            This flag is required on windows.
 :WRITE         --- [EVERY] Allows writing to the memory region.
 :EXEC          --- [EVERY] Allows executing code in the memory region.
 :NONE          --- [POSIX] Prevents accessing the memory region.

This function returns nothing useful.

This function may signal an MMAP-ERROR in case the operating system notices
a problem.

See MMAP
See MMAP-ERROR
See http://pubs.opengroup.org/onlinepubs/9699919799/functions/mprotect.html
See http://man7.org/linux/man-pages/man2/mprotect.2.html
See https://msdn.microsoft.com/en-us/library/windows/desktop/aa366898(v=vs.85).aspx")

  (function with-mmap
    "Map the file or number of bytes to a memory region within the body.

This is a convenience macro that calls MMAP with the given arguments,
binds the results to the variables ADDR, FD, and SIZE, and automatically
ensures that MUNMAP is called with the correct values when the body is
exited.

It is safe to change the ADDR, FD, and SIZE bindings, though probably not
very good style to do so. It is NOT safe to save the ADDR and SIZE values
somewhere and use them outside of the dynamic scope of the body. Attempting
to do so is very likely going to burn your process to the ground.

See MMAP
See MUNMAP"))
