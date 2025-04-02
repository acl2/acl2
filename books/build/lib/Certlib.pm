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

package Certlib;
use strict;
use warnings;
use File::Basename;
use File::Spec;
# don't know how to get it on msys
# use File::Which qw(which where);
use Storable qw(nstore retrieve);
use Cwd 'abs_path';

use Certinfo;
use Depdb;
use Bookscan;
use Cygwin_paths;

use base 'Exporter';


our @EXPORT = qw(
canonical_path
abs_canonical_path
certlib_set_opts
retrieve_cache
store_cache
certlib_add_dir
process_labels_and_targets
add_deps
add_image_deps
propagate_reqparam
to_cert_name
cert_to_acl2x
cert_to_pcert0
cert_to_pcert1
read_targets
deps_dfs
check_up_to_date
collect_bottom_out_of_date
collect_top_up_to_date
collect_top_up_to_date_modulo_local
collect_all_up_to_date
to_source_name
find_deps
write_timestamps
read_timestamps
cert_target_deps
determine_acl2_exec
determine_acl2_dirs
);


# # info about a book:
# use Class::Struct Certinfo => [ bookdeps => '@',        # books included by this one
# 				portdeps => '@',        # books included in the portcullis
# 				srcdeps => '@',         # source dependencies (.lisp, .acl2)
# 				otherdeps => '@',       # from depends_on forms
# 				image => '$',           # acl2, or from book.image/cert.image
# 				params => '%',          # cert_param entries
# 				include_dirs => '%',    # add-include-book-dir(!) forms
# 				rec_visited => '%' ];   # already seen files for depends_rec

# database -- increment this when changing the format of events produced by Bookscan.pm
my $cache_version_code = 9;

# Note: for debugging you can enable this use and then print an error message
# using
#       carp "Description of the error\n";
# and you get a backtrace as well.
use Carp;

my $debugging = 0;
my $clean_certs = 0;
my $print_deps = 0;
my $believe_cache = 0;
my $pcert_all = 0;
my $include_excludes = 0;
my $debug_up_to_date = 0;
my $force_up_to_date;
my $force_out_of_date;
my $imagefile_src_dir = 0;
# sub cert_bookdeps {
#     my ($cert, $depdb) = @_;
#     my $certinfo = $depdb->certdeps->{$cert};
#     return $certinfo ? $certinfo->bookdeps : [];
# }



#  However, now it makes sense to do it in two
# passes:
# - update the dependency-info cache, including the cert and source
# tables mentioned above
# - create the make-style dependency graph using that cache,
# afterward.

# A complication is that add-include-book-dir directives can affect
# what dependencies are stored, but this should only affect ones that
# come after.  To deal with this, for each file we'll create a log of
# what relevant lines are in it, in order.

my %dirs = ( );

sub certlib_add_dir {
    my ($name,$dir) = @_;
    $dirs{$name} = $dir;
}

sub read_projects_dirs {
    my ($acl2_projects) = @_;
    # acl2_projects should already be absolute, canonical path
    if (open (my $projects, "<", $acl2_projects)) {
	while (my $pline = <$projects>) {
	    my @parts = $pline =~ m/^\s*:(\S*)\s+"([^"]*)"/;
	    if (@parts) {
		my ($key, $dir) = @parts;
		my $dirfull;
		if (File::Spec->file_name_is_absolute($dir)) {
		    $dirfull = $dir;
		} else {
		    $dirfull = File::Spec->catfile(dirname($acl2_projects), $dir);
		}
		certlib_add_dir(uc($key), abs_canonical_path($dirfull));
	    } else {
		print(STDERR
		      "Couldn't parse ACL2_PROJECTS file line $pline\n");
	    }
	}
	close($projects);
    } else {
	print(STDERR
	      "Couldn't read ACL2_PROJECTS file $acl2_projects\n");
    }
}



sub certlib_set_opts {
    my $opts = shift;
    $debugging = $opts->{"debugging"};
    $clean_certs = $opts->{"clean_certs"};
    $print_deps = $opts->{"print_deps"};
    $believe_cache = $opts->{"believe_cache"};
    $pcert_all = $opts->{"pcert_all"};
    $include_excludes = $opts->{"include_excludes"};
    $debug_up_to_date = $opts->{"debug_up_to_date"};
    $force_up_to_date = $opts->{"force_up_to_date"};
    $force_out_of_date = $opts->{"force_out_of_date"};
    $imagefile_src_dir = $opts->{"imagefile_src_dir"};
}


sub determine_acl2_exec {
    my ($acl2) = @_;
    # If it is already set here, it has been set by command line and we won't override it.
    
    unless($acl2) {
	$acl2 = $ENV{"ACL2"};
    }
    
    unless ($acl2) {
	$acl2 = "acl2";
    }

    # convert user-provided ACL2 to cygwin path, under cygwin
    $acl2 = path_import($acl2);
    # this is probably always /dev/null but who knows under windows
    my $devnull = File::Spec->devnull;
    # get the absolute path
    $acl2 = `which $acl2 2>$devnull`;
    chomp($acl2);		# remove trailing newline

    if ($acl2) {
	# canonicalize the path
	$acl2 = abs_canonical_path($acl2);
	$ENV{"ACL2"} = $acl2;
    }
    return $acl2;
}

sub determine_acl2_dirs {
    my ($acl2_books, $acl2_projects, $acl2, $startjob, $scriptdir) = @_;
    # Determines the system books dir and imports project dirs as
    # global include-book-dirs.  If acl2_books or acl2_projects is
    # defined, then these were set by command line args and won't be
    # overridden.  Acl2 is the acl2 executable, which is run in order
    # to determine the system books as a fallback. Scriptdir is the
    # RealBin of the script itself, presumably in books/build, which
    # we use to determine the system books as another fallback.

    # Returns the final system books dir.

    # First way of setting acl2_books: command line (passed in as arg here)
    # Second way: environment var
    unless ($acl2_books) {
	$acl2_books = $ENV{"ACL2_SYSTEM_BOOKS"};
    }

    unless ($acl2_projects) {
	$acl2_projects = $ENV{"ACL2_PROJECTS"};
    }

    if ($acl2_projects) {
	$acl2_projects = abs_canonical_path($acl2_projects);
	read_projects_dirs($acl2_projects);
	# In case we're going to run Make, set the ACL2_PROJECTS
	# environment var to match our assumption.
	my $acl2_projects_env = path_export($acl2_projects);
	$ENV{"ACL2_PROJECTS"} = $acl2_projects_env;
    }

    # Third way of setting acl2_books: projects entry
    unless ($acl2_books ) {
	# Check whether the SYSTEM dir was set when reading the acl2_projects file and set it if so.
	$acl2_books = lookup_colon_dir("SYSTEM", {});

        if ($acl2_books) {
            # In this case we skip the rest because the path should be
            # canonicalized already and is already added to the $dirs.
            my $acl2_books_env = path_export($acl2_books);
            $ENV{"ACL2_SYSTEM_BOOKS"} = $acl2_books_env;
            return $acl2_books;
        }
    }
    
    # Fourth way: directory named books under the directory containing acl2
    if (! $acl2_books && $acl2 ) {
	# was:
	# my $tmp_acl2_books = rel_path(dirname($acl2), "books");
	my $tmp_acl2_books = File::Spec->catfile(dirname($acl2), "books");
	if (-d $tmp_acl2_books) {
	    $acl2_books = $tmp_acl2_books;
	}
    }
    
    my $devnull = File::Spec->devnull;
    $startjob = $startjob || "bash";
    # Fifth way: run ACL2 and have it print the system-books-dir
    if (! $acl2_books && $acl2 ) {
	my $dumper1 =		# command to send to ACL2
	    '(cw \"~%CERT_PL_VAL:~S0~%\" (acl2::system-books-dir acl2::state))';
	my $dumper2 =		# command to send to STARTJOB
	    'echo "' . $dumper1 . '" | ' .
	    "$acl2 2>$devnull | " .
	    'awk -F: "/CERT_PL_VAL/ { print \$2 }"';
	my $dumper3 =		# command to send to the shell
	    "$startjob -c '$dumper2'";
	my $tmp_acl2_books = `$dumper3`;
	chomp($tmp_acl2_books);
	if (-d $tmp_acl2_books) {
	    $acl2_books = $tmp_acl2_books;
	}
    }
    
    # Sixth: directory underneath the script directory (which we assume to be books/build)
    if (! $acl2_books ) {
	my $tmp_acl2_books = "$scriptdir/..";
	if (-d $tmp_acl2_books) {
	    $acl2_books = $tmp_acl2_books;
	}
    }

    unless ($acl2_books) {
	return undef;
    }
    
    $acl2_books = abs_canonical_path($acl2_books);
    
    # In case we're going to run Make, set the ACL2_SYSTEM_BOOKS
    # environment variable to match our assumption.
    # In cygwin, ACL2 reads paths like c:/foo/bar whereas we're dealing in
    # paths like /cygdrive/c/foo/bar, so "export" it
    certlib_add_dir("SYSTEM", $acl2_books);
    my $acl2_books_env = path_export($acl2_books);
    $ENV{"ACL2_SYSTEM_BOOKS"} = $acl2_books_env;

    return $acl2_books;

}



my %abs_path_memo = ();
# must only be called on existing paths, at least in cygwin
sub get_abs_path {
    my $path = shift;
    my $entry = $abs_path_memo{$path};
    if ($entry) {
	return $entry;
    }
    my $res = Cwd::abs_path($path);
    $abs_path_memo{$path}=$res;
    return $res;
}

# We're mostly interested in resolving directory symlinks here.
# If we have source files themselves symlinked, we won't canonicalize them
# b/c presumably they are supposed to be considered different files?
# This assumes that the file isn't necessarily supposed to exist, but the directory is.
sub abs_canonical_path {
    my $path = shift;
    # print "path: $path\n";
    my $abspath;
    if (File::Spec->file_name_is_absolute($path)) {
	# print "absolute\n";
	$abspath = $path;
    } else {
	$abspath = File::Spec->rel2abs($path);
    }
    # print "abspath: $abspath\n";
    my ($vol, $dir, $file) = File::Spec->splitpath($abspath);
    # print "path: $path vol: $vol dir: $dir file: $file\n";
    my $voldir = File::Spec->catpath($vol, $dir, "");
    # print "voldir: $voldir\n";
    if (! -d $voldir) {
	print STDERR "Oops, trying to go into $voldir\n";
	return 0;
    }
    # fast_abs_path is supposed to be faster, but it seems not to be
    # on a test system with linux over nfs etc etc.  Who knows.  Doc
    # also says fast_abs_path is "more dangerous", whatever that
    # means.
    my $absdir = get_abs_path($voldir); # Cwd::fast_abs_path($voldir);
    # print "absdir: $absdir\n";
    if ($absdir) {
	if ($file) {
	    return File::Spec->catfile($absdir, $file);
	} else {
	    return $absdir;
	}
    } else {
	print STDERR "Warning: canonical_path: Directory not found: " . $voldir . "\n";
	return 0;
    }
}

my $BASE_PATH = abs_canonical_path(".");

my %canonical_path_memo = ();

sub canonical_path_aux {
    my $fname = shift;

    my $abs_path = abs_canonical_path($fname);
    if ($BASE_PATH && $abs_path) {
	my $relpath =  File::Spec->abs2rel($abs_path, $BASE_PATH);
	return $relpath ? $relpath : ".";
    }
    return $abs_path;
}

sub canonical_path {
    my $fname = shift;
    my $entry = $canonical_path_memo{$fname};
    if ($entry) {
	return $entry;
    } else {
	my $res = canonical_path_aux($fname);
	$canonical_path_memo{$fname} = $res;
	return $res;
    }
}


sub certlib_set_base_path {
    my $dir = shift;
    $dir = $dir || ".";
    $BASE_PATH = abs_canonical_path($dir);
    %canonical_path_memo = ();
}





sub cert_to_acl2x {
    my $cert = shift;
    (my $acl2x = $cert) =~ s/\.cert$/\.acl2x/;
    return $acl2x;
}

sub cert_to_pcert0 {
    my $cert = shift;
    (my $pcert = $cert) =~ s/\.cert$/\.pcert0/;
    return $pcert;
}

sub cert_to_pcert1 {
    my $cert = shift;
    (my $pcert = $cert) =~ s/\.cert$/\.pcert1/;
    return $pcert;
}








sub to_basename {
    my $name = shift;
    $name = canonical_path($name);
    $name =~ s/\.(lisp|cert)$//;
    return $name;
}






sub lookup_colon_dir {
    my $name = uc(shift);
    my $local_dirs = shift;
    print "lookup_colon_dir $name\n" if $debugging;
    my $dirpath;
    if ($local_dirs && exists $local_dirs->{$name}) {
	$dirpath = $local_dirs->{$name};
    } else {
	$dirpath = $dirs{$name} ;
    }
    return $dirpath;
}




# Possible more general way of recognizing a Lisp symbol:
# ((?:[^\\s\\\\|]|\\\\.|(?:\\|[^|]*\\|))*)
# - repeatedly matches either: a non-pipe, non-backslash, non-whitespace character,
#                              a backslash and subsequently any character, or
#                              a pair of pipes with a series of intervening non-pipe characters.
# For now, stick with a dumber, less error-prone method.

my $timestamps = {};

sub ftimestamp {
    my $file = shift;
    if (exists $timestamps->{$file}) {
	return $timestamps->{$file};
    }
    my @statinfo = stat($file);
    if (@statinfo) {
	$timestamps->{$file} = $statinfo[9];
	return $statinfo[9];
    } else {
	$timestamps->{$file} = -1;
	return -1;
    }
}

sub write_timestamps {
    my $tsfile = shift;
    nstore($timestamps, $tsfile);
}

sub read_timestamps {
    my $tsfile = shift;
    $timestamps = retrieve($tsfile);
}

sub excludep {
    if ($include_excludes) {
	return 0;
    }
    my $prev = shift;
    my $dirname = dirname($prev);
    # Memoize this?
    while ($dirname ne $prev && basename($prev) ne "..") {
	if (-e File::Spec->catfile($dirname, "cert_pl_exclude")) {
	    # (-e rel_path($dirname, "cert_pl_exclude")) {
	    return 1;
	}
	$prev = $dirname;
	$dirname = dirname($dirname);
    }
    return 0;
}



sub print_dirs {
    # Print debugging output on stdout
    my $local_dirs = shift;
    print "dirs:\n";
    while ( (my $k, my $v) = each (%{$local_dirs})) {
	print "$k -> $v\n";
    }
}

# Gets the list of dependency-affecting events that are present in a
# source file.  These may be either already in the cache, or else they
# are read in using scan_src.
sub src_events {
    my ($fname,$evcache,$checked,$parent) = @_;

    my $entry = $evcache->{$fname};
    my $entry_ok = 0;

    if ($entry && ($believe_cache || $checked->{$fname})) {
	# Print debugging output on stdout
	print "cache believed for $fname\n" if $debugging;
	$checked->{$fname} = 1;
	$entry_ok = 1;
    }

    if (! $entry_ok && ! -e $fname) {
	print STDERR "Warning: missing file $fname";
	if ($parent) {
	    print STDERR " (required by $parent)";
	}
	else {
	    print STDERR " (no parent; top level target? cached target?)";
	}
	print STDERR "\n";
	# Add an entry with no events and a negative timestamp.
	# signalling that the file didn't exist.
	my $cache_entry =  [[], 0];
	$checked->{$fname} = 1;
	$evcache->{$fname} = $cache_entry;
	return $cache_entry->[0];
    }

    my $timestamp = ftimestamp($fname);
    # check timestamp: to be valid, the entry's timestamp must equal the file's.
    if ($entry && ! $entry_ok && ($timestamp == $entry->[1])) {
	# Print debugging output on stdout
	print "timestamp of $fname ok\n" if $debugging;
	$checked->{$fname} = 1;
	$entry_ok = 1;
    }

    if ($entry_ok) {
	# Print debugging output on stdout
	print "returning cached events for $fname\n" if $debugging;
	return $entry->[0];
    }

    print "reading events for $fname\n" if $debugging;
    my $events = scan_src($fname);
    # my $timestamp = ftimestamp($fname);
    my $cache_entry = [$events, $timestamp];
    print "caching events for $fname\n" if $debugging;
    $evcache->{$fname} = $cache_entry;
    $checked->{$fname} = 1;
    return $events;

}

sub expand_dirname_cmd {
    my ($relname,$basename,$dirname,$local_dirs,$cmd,$ext) = @_;
    my $fullname;
    if ($dirname) {
	my $dirpath = lookup_colon_dir($dirname, $local_dirs);
	unless ($dirpath) {
	    print STDERR "Warning: Unknown :dir entry in ($cmd \"$relname\" :dir $dirname) for $basename\n";
	    print_dirs($local_dirs) if $debugging;
	    return 0;
	}
	print "expand $dirname -> $dirpath\n" if $debugging;
	# was:
	# $fullname = canonical_path(rel_path($dirpath, $relname . $ext));
	$fullname = canonical_path(File::Spec->catfile($dirpath, $relname . $ext));
	if (! $fullname) {
	    print STDERR ":dir entry in ($cmd \"$relname\" :dir $dirname) produced bad path\n";
	}
    } else {
	my $dir = dirname($basename);
	my $fullpath = File::Spec->file_name_is_absolute($relname) ?
	    $relname . $ext :
	    File::Spec->catfile($dir, $relname . $ext);
	# was:
	# $fullname = canonical_path(rel_path($dir, $relname . $ext));
	$fullname = canonical_path($fullpath);
	if (! $fullname) {
	    print STDERR "bad path in ($cmd \"$relname\")\n";
	}
    }
    return $fullname;
}

sub print_event {
    my ($stream, $event) = @_;
    $stream->print($event->[0]);
    my $i = 1;
    while ($i < @$event) {
	$event->[$i] && $stream->print(" $event->[$i]");
	$i = $i+1;
    }
}

sub print_events {
    my $events = shift;
    foreach my $event (@$events) {
	print "\n"; print_event(*STDOUT, $event);
    }
    print "\n";
}

my %times_seen = ();

sub print_times_seen {
    foreach my $key (sort(keys(%times_seen))) {
	print "$key -> $times_seen{$key}\n";
    }
}

my $src_deps_depth = -1;
# Gets the (recursive) dependencies of fname, and returns whether it
# requires two-pass certification.  Calls src_events to get the
# dependency-affecting events that are present in the file
# (include-books, lds, etc.)
sub src_deps {
    my ($fname,             # file to scan for dependencies
	$depdb,             # dep database
	$certinfo,          # certinfo accumulator
        $ldp,               # allow following LD commands
	$portp,             # Add books to port rather than bookdeps
	$seen,              # seen table for detecting circular dependencies
	$parent)            # file that required this one
	= @_;

    if ($seen->{$fname}) {
	print STDERR "Circular dependency found in src_deps of $fname\n";
	return 0;
    }

    $seen->{$fname} = 1;

    $times_seen{$fname} = ($times_seen{$fname} || 0) + 1;

    $src_deps_depth = $src_deps_depth + 1;
    print "$src_deps_depth src_deps $fname\n"  if $debugging;
    my $events = src_events($fname, $depdb->evcache, $depdb->tscache, $parent);
    if ($debugging) {
	print "events: $fname";
	print_events($events);
    }
    # NOTE: We no longer check if the file exists here -- represented
    # by the tscache entry being valid

    # if (! ($believe_cache || $depdb->tscache->{$fname})) {
    # 	# The file doesn't exist.  We've already printed an error message.
    # 	return;
    # }
    push(@{$certinfo->srcdeps}, $fname);
    $depdb->sources->{$fname} = 1;

    # track the level of ifdefs
    my $ifdef_level = 0;           # nesting depth
    my $ifdef_skipping_level = 0;  # min level of a false ifdef (0 means all surrounding ifdefs were true)


    my $defines = $certinfo->local_defines;
    my $incdirs = $certinfo->local_include_dirs;

    foreach my $event (@$events) {
	my $type = $event->[0];
	if ($type eq ifdef_event) {
	    my $negate = $event->[1];
	    my $var = $event->[2];
	    my $value = exists($defines->{$var}) ? $defines->{$var} : ($ENV{$var} || "");
	    $ifdef_level = $ifdef_level + 1;
	    print "ifdef_event: negate=$negate, var=$var, new level $ifdef_level\n" if $debugging;
	    my $empty = $value eq "";
	    my $expr = (($value eq "") xor $negate);
	    my $nexpr = not $expr;
	    print "empty: $empty expr: $expr nexpr: $nexpr\n" if $debugging;
	    if (($value eq "") xor $negate) {
		if ($ifdef_skipping_level == 0) {
		    print "now skipping, level=$ifdef_level\n" if $debugging;
		    $ifdef_skipping_level = $ifdef_level;
		}
	    }
	} elsif ($type eq endif_event) {
	    print "endif_event, current level $ifdef_level\n" if $debugging;
	    if ($ifdef_skipping_level == $ifdef_level) {
		print "no longer skipping\n" if $debugging;
		$ifdef_skipping_level = 0;
	    }
	    $ifdef_level = $ifdef_level-1;
	} elsif ($ifdef_skipping_level == 0) {
	    # Only pay attention to other events if we're not skipping due to ifdefs.
	    if ($type eq add_dir_event) {
		my (undef, $name, $key, $dir, $localp) = @$event;

		print "add_dir_event: name=$name, key=$key, dir=$dir, localp=$localp\n" if $debugging;

		if ($key) {
		    my $keydir = lookup_colon_dir($key, $incdirs);
		    $dir = File::Spec->catfile($keydir, $dir);
		}

		my $newdir;
		if (File::Spec->file_name_is_absolute($dir)) {
		    $newdir = canonical_path($dir);
		}
		else {
		    # was:
		    # my $newdir = canonical_path(rel_path($basedir, $dir));
		    my $basedir = dirname($fname);
		    my $catdir = File::Spec->file_name_is_absolute($dir) ?
			$dir :
			File::Spec->catfile($basedir, $dir);
		    $newdir = canonical_path($catdir);
		}
		print "add_dir_event: newdir is $newdir\n" if $debugging;

		if (! $newdir) {
		    print STDERR "Bad path processing (add-include-book-dir :$name \"$dir\") in $fname\n";
		}
		$incdirs->{$name} = $newdir;
		if ($portp || ! $localp) {
		    print "add_dir: adding nonlocal incdir $name -> $newdir\n" if $debugging;
		    $certinfo->include_dirs->{$name} = $newdir;
		}
		print "src_deps: add_dir $name " . $newdir . "\n" if $debugging;
	    } elsif ($type eq include_book_event) {
		my (undef, $bookname, $dir, $noport, $localp) = @$event;
		my $fullname = expand_dirname_cmd($bookname, $fname, $dir,
						  $incdirs,
						  "include-book",
						  ".cert");
		if (! $fullname) {
		    print STDERR "Bad path in (include-book \"$bookname\""
			. ($dir ? " :dir $dir)" : ")") . " in $fname\n";
		} else {
		    print "include-book fullname: $fullname\n" if $debugging;
		    if ($portp) {
			push(@{$certinfo->portdeps}, $fullname);
			push(@{$certinfo->portdeps_local}, $localp);
		    } else {
			push(@{$certinfo->bookdeps}, $fullname);
			push(@{$certinfo->bookdeps_local}, $localp);
		    }
		    add_deps($fullname, $depdb, $fname);
		    my $book_certinfo = $depdb->certdeps->{$fullname};
		    if ($book_certinfo) {
			while (my ($kwd, $path) = each(%{$book_certinfo->include_dirs})) {
			    $incdirs->{$kwd} = $path;
			    if ($portp || ! $localp) {
				$certinfo->include_dirs->{$kwd} = $path;
			    }
			}
			while (my ($kwd, $val) = each(%{$book_certinfo->defines})) {
			    $defines->{$kwd} = $val;
			    if ($portp || ! $localp) {
				$certinfo->defines->{$kwd} = $val;
			    }
			}
		    } else {
			# Presumably we've printed an error message already?
		    }
		}
	    } elsif ($type eq depends_on_event) {
		my $depname = $event->[1];
		my $dir = $event->[2];
		my $fullname = expand_dirname_cmd($depname, $fname, $dir,
						  $certinfo->include_dirs,
						  "depends-on", "");
		if (! $fullname) {
		    print STDERR "Bad path in (depends-on \"$depname\""
			. ($dir ? " :dir $dir)" : ")") . " in $fname\n";
		} else {
		    push(@{$certinfo->otherdeps}, $fullname);
		    $depdb->others->{$fullname} = 1;
		}
	    } elsif ($type eq depends_rec_event) {
		my $depname = $event->[1];
		my $dir = $event->[2];
		my $fullname = expand_dirname_cmd($depname, $fname, $dir,
						  $certinfo->include_dirs,
						  "depends-rec", ".cert");
		if (! $fullname) {
		    print STDERR "Bad path in (depends-rec \"$depname\""
			. ($dir ? " :dir $dir)" : ")") . " in $fname\n";
		} else {
		    print "depends_rec $fullname\n" if $debugging;
		    add_deps($fullname, $depdb, $fname);
		    my @tmpcerts = ();
		    my @tmpothers = ();
		    deps_dfs($fullname, $depdb, $certinfo->rec_visited,
			     $certinfo->srcdeps, \@tmpcerts, \@tmpothers);
		}
	    } elsif ($type eq loads_event) {
		my $srcname = $event->[1];
		my $dir = $event->[2];
		my $fullname = expand_dirname_cmd($srcname, $fname, $dir,
						  $certinfo->include_dirs, "loads", "");
		if ($fullname) {
		    src_deps($fullname, $depdb, $certinfo, $ldp, $portp, $seen, $fname);
		} else {
		    print STDERR "Bad path in (loads \"$srcname\""
			. ($dir ? " :dir $dir)" : ")") . " in $fname\n";
		}
	    } elsif ($type eq cert_param_event) {
		my $pairs = $event->[1];
		foreach my $pair (@$pairs) {
		    (my $name, my $val) = @$pair;
		    $certinfo->params->{$name} = $val;
		}
	    } elsif ($type eq ld_event) {
		my $srcname = $event->[1];
		my $dir = $event->[2];
		my $fullname = expand_dirname_cmd($srcname, $fname, $dir,
						  $certinfo->include_dirs, "ld", "");
		if ($fullname) {
		    src_deps($fullname, $depdb, $certinfo, $ldp, $portp, $seen, $fname);
		} else {
		    print STDERR "Bad path in (ld \"$srcname\""
			. ($dir ? " :dir $dir)" : ")") . " in $fname\n";
		}
		if (! $ldp) {
		    print STDERR "Warning: LD event in book context in $fname:\n";
		    print_event(*STDERR, $event);
		    print STDERR "\n";
		}
	    } elsif ($type eq ifdef_define_event) {
		my (undef, $negate, $var, $localp) = @$event;
		my $val = $negate ? "" : "1";
		$defines->{$var} = $val;
		if ($portp || ! $localp) {
		    $certinfo->defines->{$var} = $val;
		}
	    } elsif (! ($type eq set_max_mem_event || $type eq set_max_time_event || $type eq pbs_event || $type eq cert_env_event)) {
		print STDERR "unknown event type: $type\n";
	    }
	}
    }

    $seen->{$fname} = 0;

    print "$src_deps_depth done src_deps $fname\n" if $debugging;
    $src_deps_depth = $src_deps_depth - 1;
}

sub print_lst {
    my $lst = shift;
    foreach my $val (@$lst) {
	$val && print " $val";
    }
    print "\n";
}

sub remove_dups {
    my $lst = shift;
    my @newlst = ();
    my @sortlst = sort(@$lst);
    my $lastentry = $sortlst[0];
    push (@newlst, $lastentry);
    foreach my $val (@sortlst) {
	push(@newlst, $val) unless ($val eq $lastentry);
	$lastentry = $val;
    }
    return \@newlst;
}


# Find dependencies of a lisp file.  If it has a .lisp extension, we
# assume it's supposed to be a certifiable book, so we look for .acl2
# and image files as well.  Calls src_deps to get the dependencies.
sub find_deps {
    my ($lispfile, $depdb, $parent) = @_;

    my $certinfo = new Certinfo;

    # If this source file has a .lisp extension, we assume it's a
    # certifiable book and look for an .acl2 file.
    my $certifiable = $lispfile =~ /\.lisp$/;

    my $base;
    my $certparams = {};
    if ($certifiable) {
	# If a corresponding .acl2 file exists or otherwise if a
	# cert.acl2 file exists in the directory, we need to scan that for dependencies as well.
	( $base = $lispfile ) =~ s/\.lisp$//;
	my $acl2file = $base . ".acl2";
	if (! -e $acl2file) {
	    # was:
	    # $acl2file = rel_path(dirname($base), "cert.acl2");
	    $acl2file = File::Spec->catfile(dirname($base), "cert.acl2");
	    if (! -e $acl2file) {
		$acl2file = 0;
	    }
	}

	# Scan the .acl2 file first so that we get the add-include-book-dir
	# commands before the include-book commands.
	if ($acl2file) {
	    src_deps($acl2file, $depdb, $certinfo, 1, 1, {}, $lispfile);
	}
    }

    # Scan the lisp file for include-books.
    src_deps($lispfile, $depdb, $certinfo, (! $certifiable), 0, {}, $parent);

    if ($debugging) {
	print "find_deps $lispfile: bookdeps:\n";
	print_lst($certinfo->bookdeps);
	print "sources:\n";
	print_lst($certinfo->srcdeps);
	print "others:\n";
	print_lst($certinfo->otherdeps);
    }

    if ($certifiable) {
	# Look for something indicating what saved image to use for building this file.
	# First look for an acl2-image certparam.
	my $paramimage = $certinfo->params->{"acl2-image"};

	my $imagefileimage;
	# If there is an .image file corresponding to this file or a
	# cert.image in this file's directory, add a dependency on the
	# ACL2 image specified in that file and the .image file itself.
	my $imagefile = $base . ".image";
	my $directory_imagefile;
	if (! -e $imagefile) {
	    # was:
	    # $imagefile = rel_path(dirname($base), "cert.image");
	    $imagefile = File::Spec->catfile(dirname($base), "cert.image");
	    if (! -e $imagefile) {
		$imagefile = 0;
	    } else {
		$directory_imagefile = 1;
	    }
	} else {
	    $directory_imagefile = 0;
	}

	if ($imagefile) {
	    my $imfilepath = canonical_path($imagefile);
	    # Won't check the result of canonical_path because we're
	    # already in the right directory.
	    push(@{$certinfo->otherdeps}, $imfilepath);
	    $depdb->others->{$imfilepath} = 1;
	    my $line;
	    if (open(my $im, "<", $imagefile)) {
		$line = <$im>;
		close $im;
		chomp $line;
	    } else {
		print STDERR "Warning: find_deps: Could not open image file $imagefile: $!\n";
	    }
	    $imagefileimage = $line;
	}
	if ($paramimage || $imagefileimage) {
	    if ($paramimage && $imagefileimage && ! ($paramimage eq $imagefileimage) && !$directory_imagefile) {
		print STDERR "Warning: find_deps: different acl2 images for $lispfile given by acl2-image cert-param and .image file.\n";
		print STDERR " Using image given by cert-param:     $paramimage\n";
		print STDERR " Ignoring image from .image file:     $imagefileimage\n";
	    }
	    $certinfo->image($paramimage || $imagefileimage);
	}
    }
    if ($certinfo->image && $imagefile_src_dir) {
	add_image_deps($certinfo->image, $depdb, $lispfile);
    }

    return $certinfo;

}



# Given that the dependency map $depdb is already built, this collects
# the full set of sources and targets needed for a given file.
sub deps_dfs {
    my ($target, $depdb, $visited, $sources, $certs, $others) = @_;

    if ($visited->{$target}) {
	return;
    }

    $visited->{$target} = 1;

    push (@$certs, $target);
    my $certdeps = $depdb->cert_deps($target);
    my $srcdeps = $depdb->cert_srcdeps($target);
    my $otherdeps = $depdb->cert_otherdeps($target);

    foreach my $dep (@$srcdeps) {
	if (! $visited->{$dep}) {
	    push(@$sources, $dep);
	    $visited->{$dep} = 1;
	}
    }

    foreach my $dep (@$otherdeps) {
	if (! $visited->{$dep}) {
	    push(@$others, $dep);
	    $visited->{$dep} = 1;
	}
    }


    foreach my $dep (@$certdeps) {
	deps_dfs($dep, $depdb, $visited, $sources, $certs, $others);
    }

}

# Depth-first search through the dependency map in order to propagate requirements (e.g. ccl-only)
# from books with that cert_param to books that include them.
sub propagate_reqparam {
    my ($target, $paramname, $visited, $depdb) = @_;
    if ($visited->{$target}) {
	return;
    }
    $visited->{$target} = 1;
    my $param = $depdb->cert_get_param($target, $paramname);
    if ($param) {
	if ($param == 1) {
	    # Indicates this is the book where the certparam was set.
	    # Set it to the name of the book for debugging purposes.
	    my $params = $depdb->cert_get_params($target);
	    $params->{$paramname} = $target;
	}
	return;
    }

    my $certdeps = $depdb->cert_deps($target);
    my $set_param = 0;
    foreach my $dep (@$certdeps) {
	propagate_reqparam($dep, $paramname, $visited, $depdb);
	my $dep_param = $depdb->cert_get_param($dep, $paramname);
	if ($dep_param) {
	    my $params = $depdb->cert_get_params($target);
	    $params->{$paramname} = $dep_param;
	    # print "Setting $paramname in $target due to ${dep_param} (via $dep)\n";
	    return;
	}
    }
}

sub newer_than_or_equal {
    my ($f1, $f2) = @_;
    return ftimestamp($f1) >= ftimestamp($f2);
}

# Returns a hash mapping each certificate to 1 if up to date, 0 if not.
sub check_up_to_date {
    my ($targets, $depdb) = @_;

    foreach my $key (keys(%$force_up_to_date)) {
	print("force_up_to_date $key $force_up_to_date->{$key}\n");
    }

    foreach my $key (keys(%$force_out_of_date)) {
	print("force_out_of_date $key $force_out_of_date->{$key}\n");
    }

    my %up_to_date = ();
    my $dfs;
    $dfs = sub {
	my $target = shift;
	# print "check_up_to_date dfs($target)\n";
	if (exists $up_to_date{$target}) {
	    return;
	}

	if ($force_up_to_date->{$target}) {
	    $up_to_date{$target} = 1;
	    return;
	}

	if ($force_out_of_date->{$target}) {
	    $up_to_date{$target} = 0;
	    return;
	}

	my $certdeps = $depdb->cert_deps($target);
	foreach my $cert (@$certdeps) {
	    $dfs->($cert);
	}

	if (! -e $target) {
	    $up_to_date{$target} = 0;
	    return;
	}
	foreach my $cert (@$certdeps) {
	    # note if cert is up to date then we "know" it exists
	    # (unless it was deleted since then).
	    if (! $up_to_date{$cert} || ! newer_than_or_equal($target, $cert)) {
		$up_to_date{$target} = 0;
		return;
	    }
	}
	my $srcdeps = $depdb->cert_srcdeps($target);
	my $otherdeps = $depdb->cert_otherdeps($target);

	foreach my $dep (@$srcdeps, @$otherdeps) {
	    if ( (! $force_up_to_date->{$dep}) &&
		 ($force_out_of_date->{$dep} || ! (-e $dep) || ! newer_than_or_equal($target, $dep))) {
		$up_to_date{$target} = 0;
		return;
		}
	}
	$up_to_date{$target} = 1;
    };

    foreach my $target (@$targets) {
	# print "check_up_to_date loop($target)\n";
	$dfs->($target);
    }

    return \%up_to_date;
}


sub collect_top_up_to_date {
    # up_to_date is the hash returned by check_up_to_date
    my ($targets, $depdb, $up_to_date) = @_;

    # This tracks whether each target is under an up-to-date target,
    # but also doubles as a seen list.
    my %under_up_to_date = ();
    my $dfs;
    $dfs = sub {
	my ($target, $under) = @_;
	if (exists $under_up_to_date{$target}) {
	    # Seen already. Skip, but first update under_up_to_date if
	    # it needs it.
	    if ($under) {
		$under_up_to_date{$target} = 1;
	    }
	    return;
	}
	$under_up_to_date{$target} = $under;

	my $certdeps = $depdb->cert_deps($target);
	foreach my $cert (@$certdeps) {
	    $dfs->($cert, $up_to_date->{$target});
	}
    };

    foreach my $target (@$targets) {
	$dfs->($target, 0);
    }
    my @top_up_to_date = ();
    while ((my $cert, my $updated) = each %$up_to_date) {
	if ($updated && exists $under_up_to_date{$cert} && $under_up_to_date{$cert} == 0) {
	    push (@top_up_to_date, $cert);
	}
    }
    return \@top_up_to_date;
}


sub collect_top_up_to_date_modulo_local {
    # up_to_date is the hash returned by check_up_to_date
    my ($targets, $depdb, $up_to_date) = @_;

    # We need to traverse non-up-to-date targets to find which of
    # their up-to-date nonlocal dependencies need including.  We also
    # traverse up-to-date targets to mark those that are included
    # nonlocally under another up-to-date target (and therefore don't
    # need to be included separately since they will be included by
    # the ancestor).

    # This tracks whether each target is under an up-to-date target,
    # but also doubles as a seen list.
    my %under_up_to_date = ();
    my $INDENT = "";
    my $dfs;
    $dfs = sub {
	my ($target, $under) = @_;
	if (exists $under_up_to_date{$target}) {
	    # Seen already. Skip, but first update under_up_to_date if
	    # it needs it.
	    if ($under) {
		print STDERR "${INDENT}$target set as under up to date $under\n" if $debug_up_to_date;
		$under_up_to_date{$target} = $under;
	    } else {
	    	print STDERR "${INDENT}$target already seen\n" if $debug_up_to_date;
	    }
	    return;
	}
	$under_up_to_date{$target} = $under;
	my $uptodate = $up_to_date->{$target} ? $target : 0;
	if ($debug_up_to_date) {
	    if ($uptodate) {
		if ($under) {
		    print STDERR "${INDENT}$target up to date (under $under)\n";
		} else {
		    print STDERR "${INDENT}$target up to date\n";
		}
	    } else {
		print STDERR "${INDENT}$target out of date\n";
	    }
	}
	my $certdeps = $depdb->cert_nonlocal_deps($target);
	foreach my $cert (@$certdeps) {
	    my $saved_indent = $INDENT;
	    $INDENT = "${INDENT} " if $debug_up_to_date;
	    $dfs->($cert, $uptodate);
	    $INDENT = $saved_indent;
	}
    };

    foreach my $target (@$targets) {
	$dfs->($target, 0);
    }
    my @top_up_to_date = ();
    while ((my $cert, my $updated) = each %$up_to_date) {
	if ($updated && exists $under_up_to_date{$cert} && ! $under_up_to_date{$cert}) {
	    push (@top_up_to_date, $cert);
	}
    }
    return \@top_up_to_date;
}



sub collect_all_up_to_date {
    # up_to_date is the hash returned by check_up_to_date
    my ($targets, $depdb, $up_to_date) = @_;

    my @all_up_to_date = ();
    my @all_out_of_date = ();
    my %visited = ();
    my $dfs;
    $dfs = sub {
	my $target = shift;
	if ($visited{$target}) {
	    return;
	}
	$visited{$target} = 1;
	my $certdeps = $depdb->cert_deps($target);
	foreach my $cert (@$certdeps) {
	    $dfs->($cert);
	}
	if ($up_to_date->{$target}) {
	    push (@all_up_to_date, $target);
	} else {
	    push (@all_out_of_date, $target);
	}
    };

    foreach my $target (@$targets) {
	$dfs->($target);
    }

    return (\@all_up_to_date, \@all_out_of_date);
}


sub collect_bottom_out_of_date {
    # up_to_date is the hash returned by check_up_to_date
    my ($targets, $depdb, $up_to_date) = @_;

    my @bottom_out_of_date = ();
    my %visited = ();
    my $dfs;
    $dfs = sub {
	my $target = shift;

	if ($visited{$target} || $up_to_date->{$target}) {
	    return $up_to_date->{$target};
	}
	$visited{$target} = 1;
	my $bottom = 1;
	foreach my $dep (@{$depdb->cert_deps($target)}) {
	    if (! $dfs->($dep)) {
		# out of date, but not bottommost
		$bottom = 0;
	    }
	}

	if ($bottom) {
	    push(@bottom_out_of_date, $target);
	}
	return 0;
    };

    foreach my $target (@$targets) {
	$dfs->($target);
    }

    return \@bottom_out_of_date;

}


sub clean_generated_files {
    my ($base) = @_;

    my @exts = ( ".cert",
		 ".cert.out",
		 ".cert.time",
		 ".acl2x",
		 ".lx64fsl",
		 "\@expansion.lsp",
		 ".date",
		 ".cert.temp",
		 ".pcert0",
		 ".pcert1",
		 ".pcert0.temp",
		 ".port",
		 ".h",
		 ".c",
		 ".data",
		 ".o",
		 ".sbin",
		 ".lbin",
		 ".fasl",
		 ".ufsl",
		 ".64ufasl",
		 ".ufasl",
		 ".pfsl",
		 ".dfsl",
		 ".dx32fsl",
		 ".lx32fsl",
		 ".d64fsl",
		 ".dx64fsl",
		 ".lx64fsl",
		 ".bin",
		 ".sparcf",
		 ".axpf",
		 ".x86f",
		 ".ppcf",
		 ".fas",
		 ".lib"
	);
    foreach my $ext (@exts) {
	my $tmpfile = $base . $ext;
	unlink($tmpfile) if (-e $tmpfile);
    }
}


# During a dependency search, this is run with $target set to each
# cert and source file in the dependencies of the top-level targets.
# If the target has been seen before, then it returns immediately.
# Otherwise, this calls on find_deps to get those dependencies.
sub add_deps {
    my ($target, $depdb, $parent) = @_;

    print "add_deps (check) $target\n" if $debugging;

    if ($target !~ /\.cert$/) {
	print "not cert\n" if $debugging;
	return;
    }

    if (exists $depdb->certdeps->{$target}) {
	# We've already calculated this file's dependencies, or we're in a self-loop.
	if ($depdb->certdeps->{$target} == 0) {
	    print STDERR "Dependency loop on $target!\n";
	    print STDERR "Current stack:\n";
	    foreach my $book (@{$depdb->stack}) {
		print STDERR "   $book\n";
	    }
	}
	print "depdb entry exists\n" if $debugging;
	return;
    }

    if (excludep($target)) {
	print "excludep\n" if $debugging;
    	return;
    }

    $depdb->certdeps->{$target} = 0;

    print "add_deps $target\n" if $debugging;

    (my $base = $target) =~ s/\.cert$//;
    my $lispfile = $base . ".lisp";

    # Clean the cert and out files, etc., if we're cleaning.
    clean_generated_files($base) if ($clean_certs);

    # First check that the corresponding .lisp file exists.
    # if (! -e $lispfile) {
    # 	print "Error: Need $lispfile to build $target"
    #            . ($parent ? " (parent: $parent)" : "")
    # 	       . ".\n";
    # 	delete $depdb->certdeps->{$target};
    # 	return;
    # }

    # print "add_deps $target, current stack:\n";
    # foreach my $book (@{$depdb->stack}) {
    # 	print "   $book\n";
    # }
    # print "\n";

    push (@{$depdb->stack}, $target);

    my $certinfo = find_deps($lispfile, $depdb, $parent);

    my $topstack = pop(@{$depdb->stack});
    if (! ($topstack eq $target) ) {
	print STDERR "Stack discipline failed on $target! was $topstack\n";
    }

    $depdb->certdeps->{$target} = $certinfo ;

    if ($print_deps) {
        print "Dependencies for $target:\n";
        print "book:\n";
        foreach my $dep (@{$certinfo->bookdeps}) {
            print "$dep\n";
        }
        print "src:\n";
        foreach my $dep (@{$certinfo->srcdeps}) {
            print "$dep\n";
        }
        print "other:\n";
        foreach my $dep (@{$certinfo->otherdeps}) {
            print "$dep\n";
        }
        print "image: " . $certinfo->image . "\n" if $certinfo->image;
        if ($certinfo->params) {
            print "params:\n";
            while (my ($key, $value) = each %{$certinfo->params}) {
                print "$key = $value\n";
            }
            print "\n";
        }
        print "\n";
    }

    # # Accumulate the set of sources.  We haven't checked yet if they exist.
    # foreach my $dep (@$srcdeps) {
    # 	$sources->{$dep} = 1;
    # }

    # # Accumulate the set of non-source/cert deps..
    # foreach my $dep (@$otherdeps) {
    # 	$others->{$dep} = 1;
    # }


    # # Run the recursive add_deps on each dependency.
    # foreach my $dep  (@$bookdeps, @$portdeps, @$recdeps) {
    # 	add_deps($dep, $cache, $depdb, $sources, $others, $tscache, $target);
    # }

    # # Collect the recursive dependencies of @$recdeps and add them to srcdeps.
    # if (@$recdeps) {
    # 	my $recsrcs = [];
    # 	my $reccerts = [];
    # 	my $recothers = [];
    # 	my $visited = {};
    # 	foreach my $dep (@$recdeps) {
    # 	    deps_dfs($dep, $depdb, $visited, $recsrcs, $reccerts, $recothers);
    # 	}

    # 	push(@{$depdb->{$target}->[2]}, @$recsrcs);
    # }

}



sub add_image_deps {
    my ($target, $depdb, $parent) = @_;
    if ($target eq "acl2") {
	return;
    }

    print "add_image_deps (check) $target\n" if $debugging;
    my $targetimage = ${target} . ".image";

    if (exists $depdb->certdeps->{$targetimage}) {
	# We've already calculated this file's dependencies, or we're in a self-loop.
	if ($depdb->certdeps->{$targetimage} == 0) {
	    print STDERR "Dependency loop on $target!\n";
	    print STDERR "Current stack:\n";
	    foreach my $book (@{$depdb->stack}) {
		print STDERR "   $book\n";
	    }
	}
	print "depdb entry exists\n" if $debugging;
	return;
    }

    if (excludep($target)) {
	print "excludep\n" if $debugging;
    	return;
    }

    if (! $imagefile_src_dir) {
	print STDERR "Can't get dependencies of saved image $target because --image-sources/ACL2_IMAGE_SRC_DIR isn't set.\n";
	$depdb->certdeps->{$targetimage} = new Certinfo;
	return;
	
    }
    # We need to somehow map from the image name to the location of
    # the source file. For now, we're just going to use a configured
    # path for all images; will need to revisit this later.
    my $lspfile = canonical_path(File::Spec->catfile($imagefile_src_dir, $target . ".lsp"));

    if (! -e $lspfile) {
	# The file doesn't exist in the expected place.
	print STDERR "Skipping dependencies of saved image $target -- build file not found in image source dir\n";
	$depdb->certdeps->{$targetimage} = new Certinfo;
	return;
    }
    
    $depdb->certdeps->{$targetimage} = 0;

    print "add_image_deps $target\n" if $debugging;

    # What should we do when cleaning?  Delete images?  Leave it for now
    # clean_generated_files($base) if ($clean_certs);


    push (@{$depdb->stack}, $targetimage);

    my $certinfo = find_deps($lspfile, $depdb, $parent);

    my $topstack = pop(@{$depdb->stack});
    if (! ($topstack eq $targetimage) ) {
	print STDERR "Stack discipline failed on $targetimage! was $topstack\n";
    }

    $depdb->certdeps->{$targetimage} = $certinfo ;

    if ($print_deps) {
        print "Dependencies for $target:\n";
        print "book:\n";
        foreach my $dep (@{$certinfo->bookdeps}) {
            print "$dep\n";
        }
        print "src:\n";
        foreach my $dep (@{$certinfo->srcdeps}) {
            print "$dep\n";
        }
        print "other:\n";
        foreach my $dep (@{$certinfo->otherdeps}) {
            print "$dep\n";
        }
        print "image: " . $certinfo->image . "\n" if $certinfo->image;
        if ($certinfo->params) {
            print "params:\n";
            while (my ($key, $value) = each %{$certinfo->params}) {
                print "$key = $value\n";
            }
            print "\n";
        }
        print "\n";
    }

    # # Accumulate the set of sources.  We haven't checked yet if they exist.
    # foreach my $dep (@$srcdeps) {
    # 	$sources->{$dep} = 1;
    # }

    # # Accumulate the set of non-source/cert deps..
    # foreach my $dep (@$otherdeps) {
    # 	$others->{$dep} = 1;
    # }


    # # Run the recursive add_deps on each dependency.
    # foreach my $dep  (@$bookdeps, @$portdeps, @$recdeps) {
    # 	add_deps($dep, $cache, $depdb, $sources, $others, $tscache, $target);
    # }

    # # Collect the recursive dependencies of @$recdeps and add them to srcdeps.
    # if (@$recdeps) {
    # 	my $recsrcs = [];
    # 	my $reccerts = [];
    # 	my $recothers = [];
    # 	my $visited = {};
    # 	foreach my $dep (@$recdeps) {
    # 	    deps_dfs($dep, $depdb, $visited, $recsrcs, $reccerts, $recothers);
    # 	}

    # 	push(@{$depdb->{$target}->[2]}, @$recsrcs);
    # }

}



sub read_targets {
    my ($fname,$targets) = @_;
    if (open (my $tfile, $fname)) {
	while (my $the_line = <$tfile>) {
	    chomp($the_line);
	    $the_line =~ m/^\s*([^\#]*[^\#\s])?/;
	    my $fname = $1;
	    if ($fname && (length($fname) > 0)) {
		push (@{$targets}, $fname);
	    }
	}
	close $tfile;
    } else {
	print STDERR "Warning: Could not open $fname: $!\n";
    }
}

# Heuristically take some user-input filename and produce the source
# file we actually want to read.  For now, if it doesn't have a dot,
# tack a .lisp onto it; if it has a .cert/.pcert/.acl2x extension
# change it to .lisp, and otherwise leave it alone.
# examples:
# foo.lisp  -> foo.lisp
# foo       -> foo.lisp
# foo.cert  -> foo.lisp
# foo.acl2x -> foo.lisp
# foo.pcert -> foo.lisp
# foo.lsp   -> foo.lsp
# foo.acl2  -> foo.acl2
sub to_source_name {
    my $fname = shift;
    if ($fname =~ /\./) {
	$fname =~ s/\.(cert|acl2x|pcert0|pcert1)$/\.lisp/;
	return $fname;
    } else {
	return "$fname.lisp";
    }
}

# Heuristically take some user-input filename and produce the cert
# file we want to target.  For now, if it has a .lisp extension change
# it to .cert, if it has a .acl2x/.pcert/.cert extension leave it
# alone, and otherwise tack on a .cert.  NOTE: This heuristic doesn't
# at all match the one in to_source_name; they're used for different
# purposes.  (This assumes that $target_ext is cert, which is the
# default.)
# foo.lisp  -> foo.cert
# foo       -> foo.cert
# foo.cert  -> foo.cert
# foo.acl2x -> foo.acl2x
# foo.pcert -> foo.pcert
# foo.lsp   -> foo.lsp.cert
# foo.acl2  -> foo.acl2.cert
sub to_cert_name {
    my ($fname, $target_ext) = @_;
    $fname =~ s/\.lisp$//;
    if ($fname =~ /\.(cert|acl2x|pcert0|pcert1)$/) {
	return $fname;
    } else {
	return "$fname.${target_ext}";
    }
}


# Takes a list of inputs containing some filenames and some labels
# (ending with a colon) and some entries of the form "-p filename".
# Sorts out the filenames into a list of targets (changing them to
# .cert extensions if necessary) and returns the list of targets and a
# hash associating each label with its list of targets.
sub process_labels_and_targets {
    my ($input, $depdb, $target_ext) = @_;
    my %labels = ();
    my @targets = ();
    my @images = ();
    my $label_started = 0;
    my $label_targets;
    foreach my $str (@$input) {
	if (substr($str, 0, 3) eq '-p ') {
	    # Deps-of.
	    my $name = canonical_path(to_source_name(substr($str,3)));
	    if ($name) {
		my $certinfo = find_deps(to_source_name($name), $depdb, 0);
		push (@targets, @{$certinfo->bookdeps});
		push (@targets, @{$certinfo->portdeps});
		push (@$label_targets, @{$certinfo->bookdeps}) if $label_started;
		push (@images, $certinfo->image) if $certinfo->image;
	    } else {
		print STDERR "Bad path for target: $str\n";
	    }
	} elsif (substr($str, 0, 3) eq '-g ') {
	    # Image.
	    my $imgname = substr($str,3);
	    push (@images, $imgname);
	} elsif (substr($str, -1, 1) eq ':') {
	    # label.
	    my $label = substr($str,0,-1); # everything but the :
	    $label_started = 1;
	    if (! exists($labels{$label})) {
		$label_targets = [];
		$labels{$label} = $label_targets;
	    } else {
		$label_targets = $labels{$label};
	    }
	} else {
	    # filename.

	    # BOZO We should check for cert_pl_excluded files here and
	    # complain about them for top-level command-line targets.
	    # But we probably need to rework the horrible hackery of
	    # this function first.  We can't currently distinguish
	    # between command-line targets and ones from --targets
	    # files, so for now we'll remain silent.

	    my $target = canonical_path(to_cert_name($str, $target_ext));
	    if ($target) {
		push(@targets, $target);
		push(@$label_targets, $target) if $label_started;
	    } else {
		print STDERR "Bad path for target: $str\n";
	    }
	}
    }
    # print "Labels:\n";
    # while ((my $key, my $value) = each %labels) {
    # 	print "${key}:\n";
    # 	foreach my $target (@$value) {
    # 	    print "$target\n";
    # 	}
    # }

    return (\@targets, \@images, \%labels);
}



sub store_cache {
    my ($cache, $fname) = @_;
    if ($fname) {
	nstore([$cache_version_code, $cache], $fname);
    }
}

sub retrieve_cache {
    my $fname = shift;
    if (! $fname || ! -e $fname) {
	return {};
    }

    my $pair = retrieve($fname);
    if (! (ref($pair) eq 'ARRAY')) {
	print STDERR "Invalid cache format; starting from empty cache\n";
	return {};
    } elsif ( $pair->[0] != $cache_version_code ) {
	print STDERR "Wrong cache version code; starting from empty cache\n";
	return {};
    } elsif (! (ref($pair->[1]) eq 'HASH')) {
	print STDERR "Right cache version code, but badly formatted! Starting from empty\n";
	return {};
    } else {
	return $pair->[1];
    }
}

sub cert_target_deps {
    # Returns the list of cert, pcert0, pcert1, acl2x files that a
    # given file depends on, which itself may be a cert, pcert0,
    # pcert1, or acl2x file.
    my ($depdb, $target) = @_;
    my $certinfo = $depdb->certdeps->{$target};
    if ($target =~ m{\.cert$}) {
	my @res = ();
	my $deps = $depdb->cert_deps($target);
	push(@res, @$deps);
	if ($depdb->cert_get_param($target, "acl2x")) {
	    push(@res, cert_to_acl2x($target));
	} elsif ($depdb->cert_get_param($target, "pcert") || $pcert_all) {
	    push(@res, cert_to_pcert1($target));
	}
	return \@res;
    } elsif ($target =~ m{\.acl2x$}) {
	my @res = ();
	(my $cert = $target) =~ s/\.acl2x$/\.cert/;
	my $deps = $depdb->cert_deps($cert);
	push(@res, @$deps);
	return \@res;
    } elsif ($target =~ m{\.pcert1$}) {
	(my $pcert0 = $target) =~ s/\.pcert1$/\.pcert0/;
	return [ $pcert0 ];
    } elsif ($target =~ m{\.pcert0$}) {
	(my $cert = $target) =~ s/\.pcert0$/\.cert/;
	my @res = ();
	my $deps = $depdb->cert_deps($cert);
	foreach my $dep (@$deps) {
	    push(@res, $depdb->cert_sequential_dep($dep));
	}
	return \@res;
    }
    return [];
}


# The following "1" is here so that loading this file with "do" or "require" will succeed:
1;
