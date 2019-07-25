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

package Depdb;
use strict;
use warnings;

# use base 'Exporter';

# our @EXPORT = qw(
# cert_bookdeps
# cert_portdeps
# cert_deps
# cert_srcdeps
# cert_otherdeps
# cert_image
# cert_get_params
# cert_get_param
# cert_is_two_pass
# cert_sequential_dep
# cert_include_dirs
# );


use Class::Struct Depdb => [ evcache => '%',   # event cache for src files
			     certdeps => '%',  # certinfo for each book
			     sources => '%',   # set of source files
			     others  => '%',   # set of non-book dependency files
			     stack => '@',     # add_deps traversal stack
			     tscache => '%',   # cache of src file timestamps
			     pcert_all => '$'];# are we in pcert_all mode


sub cert_bookdeps {
    my ($self, $cert) = @_;
    my $certinfo = $self->certdeps->{$cert};
    return $certinfo ? $certinfo->bookdeps : [];
}

sub cert_nonlocal_bookdeps {
    my ($self, $cert) = @_;
    my $certinfo = $self->certdeps->{$cert};
    if (! $certinfo) {
	return [];
    }
    my @nonlocals = ();
    for my $i (0 .. $#{$certinfo->bookdeps}) {
	if (! $certinfo->bookdeps_local->[$i]) {
	    push (@nonlocals, $certinfo->bookdeps->[$i]);
	}
    }
    return \@nonlocals;
}


sub cert_portdeps {
    my ($self, $cert) = @_;
    my $certinfo = $self->certdeps->{$cert};
    return $certinfo ? $certinfo->portdeps : [];
}

sub cert_nonlocal_portdeps {
    my ($self, $cert) = @_;
    my $certinfo = $self->certdeps->{$cert};
    if (! $certinfo) {
	return [];
    }
    my @nonlocals = ();
    for my $i (0 .. $#{$certinfo->portdeps}) {
	if (! $certinfo->portdeps_local->[$i]) {
	    push (@nonlocals, $certinfo->portdeps->[$i]);
	}
    }
    return \@nonlocals;
}


sub cert_deps {
    my ($self, $cert) = @_;
    return [ @{$self->cert_bookdeps($cert)},
	     @{$self->cert_portdeps($cert)} ];
}

sub cert_nonlocal_deps {
    my ($self, $cert) = @_;
    return [ @{$self->cert_nonlocal_bookdeps($cert)},
	     @{$self->cert_nonlocal_portdeps($cert)} ];
}

sub cert_srcdeps {
    my ($self, $cert) = @_;
    my $certinfo = $self->certdeps->{$cert};
    return $certinfo ? $certinfo->srcdeps : [];
}

sub cert_otherdeps {
    my ($self, $cert) = @_;
    my $certinfo = $self->certdeps->{$cert};
    return $certinfo ? $certinfo->otherdeps : [];
}

sub cert_image {
    my ($self, $cert) = @_;
    my $certinfo = $self->certdeps->{$cert};
    return $certinfo && $certinfo->image;
}

sub cert_get_params {
    my ($self, $cert) = @_;
    my $certinfo = $self->certdeps->{$cert};
    return $certinfo ? $certinfo->params : {};
}

sub cert_get_param {
    my ($self, $cert, $param) = @_;
    my $params = $self->cert_get_params($cert);
    return $params->{$param};
}

sub cert_is_two_pass {
    my ($certfile, $deps) = @_;
    return cert_get_param($certfile, $deps, "acl2x");
}

sub cert_sequential_dep {
    # Assuming we're doing a provisional certification of some parent
    # book, find the sequential dependency on certfile.  This is
    # different depending on whether certfile uses provisional
    # certification, two-pass certification, etc.
    my ($self, $certfile) = @_;
    my $res;
    if ($self->cert_get_param($certfile, "acl2x")) {
	# NOTE: ACL2 doesn't allow an include-book of a book with an .acl2x but no
	# .pcert* or .cert file during a (provisional or final) certification.
	# ($res = $certfile) =~ s/\.cert$/\.acl2x/;
	$res = $certfile;
    } elsif ($self->cert_get_param($certfile, "pcert") || $self->pcert_all) {
	($res = $certfile) =~ s/\.cert$/\.pcert0/;
    } else {
	$res = $certfile;
    }
    return $res;
}

sub cert_include_dirs {
    my ($self, $cert) = @_;
    my $certinfo = $self->certdeps->{$cert};
    return $certinfo ? $certinfo->include_dirs : {};
}



1;
