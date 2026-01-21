;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(in-package :z3-c)

(define-foreign-library libz3
  (:darwin (:or "libz3.4.dylib" "libz3.dylib"))
  (:unix (:or "libz3.so.4" "libz3.so"))
  (t (:default "libz3")))

#|

To help cffi find the Z3 library and header files, you may need to do
the following:

1) update your CPATH environment variable to include the directory
where z3.h is included and

2) update your LD_LIBRARY_PATH environment variable to include the
directory where your libz3.dylib or libz3.so file is

For example in my .bashrc file I have:

export CPATH=$HOME/bin/include
export LD_LIBRARY_PATH=$HOME/bin/lib

Note that on recent version of macOS, the above may not work unless
you disable SIP. If all else fails, you can directly modify the
*foreign-library-directories* variable of cffi, by commenting out the
below line and updating the path (the first argument) to point to the
additional library path to search:

|#

;; (pushnew #P"/Users/pete/bin/lib/" *foreign-library-directories* :test #'equal)

(use-foreign-library libz3)
