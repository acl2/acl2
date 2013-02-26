
use POSIX;

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
