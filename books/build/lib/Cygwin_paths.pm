# cert.pl build system
# Copyright (C) 2008-2014 Centaur Technology
#
# Contact:
#   Centaur Technology Formal Verification Group
#   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
#   http://www.centtech.com/
#
# License: (An MIT/X11-style license)
#
#   Permission is hereby granted, free of charge, to any person obtaining a
#   copy of this software and associated documentation files (the "Software"),
#   to deal in the Software without restriction, including without limitation
#   the rights to use, copy, modify, merge, publish, distribute, sublicense,
#   and/or sell copies of the Software, and to permit persons to whom the
#   Software is furnished to do so, subject to the following conditions:
#
#   The above copyright notice and this permission notice shall be included in
#   all copies or substantial portions of the Software.
#
#   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
#   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
#   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
#   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
#   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
#   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
#   DEALINGS IN THE SOFTWARE.
#
# Original author: Sol Swords <sswords@centtech.com>

package Cygwin_paths;
use POSIX;
use base 'Exporter';
our @EXPORT = qw(path_import path_export);

# This is a gross hack to support cygwin.  Cygwin is special
# because it has its own filename conventions that are basically
# Unix-like, but these aren't compatible with the sorts of filenames
# ACL2 is expecting.  E.g., what in Windows proper is
 #  C:\home\books\foo.lisp
# is in Cygwin
#  /cygdrive/c/home/books/foo.lisp
# and what ACL2 wants to see is:
#  c:/home/books/foo.lisp.
# Cygwin can produce this using a tool called cygpath, but man, what a mess.

# Note about msys.  Msys is the other way of getting a Unixy
# environment on Windows, and we'll try to support it too.  Msys has
# its own path conventions, e.g., the above path would be
#  /c/home/books/foo.lisp.
# But nothing in this file has anything to do with msys.  Why?
# Supposedly, msys automatically converts arguments from internal
# paths to Windows-native paths when running programs (i.e. presumably
# ACL2) that don't depend on msys-1.0.dll -- see
#    http://www.mingw.org/wiki/Posix_path_conversion
# And they don't offer any way of overriding this conversion or any
# utility to do these conversions on demand.  So, we're just going to
# assume they're doing everything right.


# first we have to know whether we're on cygwin or not.
# my $in_cygwin = `uname` =~ /^CYGWIN/;
(my $sysname) = POSIX::uname();
my $in_cygwin = $sysname =~ /^CYGWIN/;

# This imports a path into our scripting world, where everything is
# basically in cygwin-land if we're using cygwin.
sub path_import {
    my $path = shift;
    if ($in_cygwin) {
	my $impath = `cygpath -u '$path'`;
	chomp($impath);
	return $impath;
    }
    return $path;
}

sub path_export {
    my $path = shift;
    if ($in_cygwin) {
	my $expath = `cygpath -m '$path'`;
	chomp($expath);
	return $expath;
    }
    return $path;
}

1;
