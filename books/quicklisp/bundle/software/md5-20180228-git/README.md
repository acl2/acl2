[![Build Status](https://travis-ci.org/pmai/md5.svg?branch=master)](https://travis-ci.org/pmai/md5)

This package implements The MD5 Message-Digest Algorithm, as defined
in [RFC 1321][] by R. Rivest, published April 1992.

It was originally written by Pierre R. Mai, with copious input from
the cmucl-help mailing-list hosted at cons.org, in November 2001 and
has been placed into the public domain.  In the meantime various fixes
and improvements for other implementations as well as maintenance have
been provided by Christophe Rhodes, Alexey Dejneka, Nathan Froyd,
Andreas Fuchs, John Desoi, Dmitriy Ivanov, and Kevin M. Rosenberg, and
have been reintegrated into this consolidated version by Pierre R. Mai.

**WARNING:** The MD5 Message-Digest Algorithm has been compromised as a
cryptographically secure hash for some time, with known theoretical
and practical attacks.  Therefore use of this implemenation is only
recommended for legacy uses or uses which do not require a
cryptographically secure hash.  Use one of the newer SHA-2 and SHA-3
secure hash standards, or whatever is currently deemed
cryptographically secure for all other uses.

This software is "as is", and has no warranty of any kind.  The
authors assume no responsibility for the consequences of any use of
this software.

[RFC 1321]: https://tools.ietf.org/html/rfc1321
