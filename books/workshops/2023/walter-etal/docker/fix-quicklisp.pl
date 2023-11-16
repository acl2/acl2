use strict;
use warnings;
use autodie;

my $home_directory = $ENV{HOME};

sub rewrite_file {
    my $file = shift;

    # You can still read from $in after the unlink, the underlying
    # data in $file will remain until the filehandle is closed.
    # The unlink ensures $in and $out will point at different data.
    open my $in, "<", $file;
    unlink $file;

    # This creates a new file with the same name but points at
    # different data.
    open my $out, ">", $file;

    return ($in, $out);
}

my $version_file = "$home_directory/quicklisp/quicklisp/version.txt";
open(my $fh, '<:encoding(UTF-8)', $version_file)
  or die "Could not open file '$version_file' $!";
my $version = <$fh>;
close($fh);
$version =~ s/[^a-zA-Z0-9,]//g; # remove all non-alphanum chars

#local $\ = "";
#print "$version";
#local $\ = "\n";

my $in = "$home_directory/quicklisp/quicklisp/quicklisp.asd";
my $out;
my($in, $out) = rewrite_file($in, $out);

my $to_replace = "#.(remove-if-not #'digit-char-p ql-info:*version*)";

# Read from $in, write to $out as normal.
while(my $line = <$in>) {
    $line =~ s/\Q$to_replace\E/"$version"/g;
    print $out $line;
}

print "Patched quicklisp.asd\n";
