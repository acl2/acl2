[![Build Status](https://github.com/cl-plus-ssl/cl-plus-ssl/actions/workflows/test.yml/badge.svg)](https://github.com/cl-plus-ssl/cl-plus-ssl/actions)

# CL+SSL

A Common Lisp interface to OpenSSL / LibreSSL.


## About

Distinguishing features: CL+SSL is portable code based on CFFI and gray
streams. It defines its own libssl BIO_METHOD, so that TLS I/O can be
written over portable Lisp streams instead of bypassing the streams and
giving OpenSSL a socket file descriptor to send data over. (But the file
descriptor approach is still used if possible.)

License: MIT-style.


## Download

The library is available via [Quicklisp](http://www.quicklisp.org/).

The Git repository: <https://github.com/cl-plus-ssl/cl-plus-ssl>.

Send bug reports to the GitHub issue tracker. The old mailing list
[cl-plus-ssl-devel@common-lisp.net](mailto:cl-plus-ssl-devel@common-lisp.net)
is also still available
([list information](http://common-lisp.net/cgi-bin/mailman/listinfo/cl-plus-ssl-devel)). 


## OpenSSL / LibreSSL Installation Hints

### Unix-like

Usually OpenSSL / LibreSSL shared libraries are provided by your package manager
and very likely are already installed.

### Windows

<https://wiki.openssl.org/index.php/Binaries> lists several sources of binary distributions. For example, <http://www.slproweb.com/products/Win32OpenSSL.html> (slproweb.com is a 3rd party; if you have questions about the OpenSSL installer they provide, please ask in the mailing list specified on the linked page).

If you chose to install the DLLs into the OpenSSL installation's "bin" directory (recommended), then be sure to add the bin directory to your PATH environment variable and restart your session. e.g. "C:\Program Files\OpenSSL-Win64\bin"

## API

Browable package definitions - click on a symbol to navigate
to the definition and read docstring:
  - <https://cl-plus-ssl.github.io/cl-plus-ssl/package.html>
  - <https://cl-plus-ssl.github.io/cl-plus-ssl/config.html>

A single HTML page dump of all exported symbols with
their docstrings and parameters:
<https://cl-plus-ssl.github.io/cl-plus-ssl/cl-plus-ssl-api.html>

## Usage

Basically, after TCP connection is created, we wrap the TCP socket stream
into a TLS encrypted stream using `cl+ssl:make-ssl-client-stream`,
or `cl+ssl:make-ssl-server-stream`. See how it's done in the
[examples/example.lisp](examples/example.lisp). That's a
self-contained file, you can load it or copy-paste into your
Slime session and try the examples as suggested in the comments at the
top of the file.

For more comfortable use learn some of OpenSSL API. In particular
that SSL object represents a TLS session, SSL_CTX object is a
context multiple SSL objects can derive from thus sharing
common parameters. BIO is a stream-like input/output abstraction
OpenSSL uses for actual data transfer. That OpenSSL API
uses reference counting; therefore, for example, if an SSL
object is derived from an SSL_CTX, we can apply SSL_CTX_free
to the SSL_CTX when the SSL is still being used - our call
will just decrement the reference count so if the SSL
holds another reference to the SSL_CTX, the SSL_CTX will remain
alive and will only be destroyed after the SSL releases
this reference.

Knowing OpenSSL will also allow for more flexibility and control,
as cl+ssl high-level functions do not cover all possible approaches.

### Lisp BIO or Socket BIO.

OpenSSL comes with several BIO implementations, like file BIO,
socket BIO, memory BIO, etc. Also OpenSSL API allows user to
create custom BIO methods by providing a number of callbacks.

cl+ssl uses either socket BIO, or a custom BIO that implements
all input / output with Lisp functions like `cl:write-byte`,
`cl:read-byte`.

When a Lisp stream is passed to `cl+ssl:make-ssl-client-stream`
or `cl+ssl:make-ssl-server-stream`, the choice of BIO is made
based on the `:unwrap-stream-p` parameter.

If `:unwrap-stream-p` is true, a socket file descriptor is extracted
from the Lisp stream and passed to OpenSSL using the `SSL_set_fd`
OpenSSL function, which results in socket BIO created for
that SSL session.

If `:unwrap-stream-p` is false, a Lisp BIO is created and
passed to OpenSSL with the `SSL_set_bio` OpenSSL funcion.

The default value of `:unwrap-stream-p` is special variable
`cl+ssl:*default-unwrap-stream-p*` which is initialized to `t`,
meaning socket BIO is used by default.

This allows to dynamically change the mode of operation of the
code that omits the `:unwrap-stream-p` parameter.

For the `test-https-client` function from the example.lisp:

```common-lisp

    ;; use socket BIO

    (let ((cl+ssl:*default-unwrap-stream-p* t))
      (tls-example::test-https-client "www.google.com"))

    ;; use Lisp BIO

    (let ((cl+ssl:*default-unwrap-stream-p* nil))
      (tls-example::test-https-client "www.google.com"))

```

If `cl+ssl:make-ssl-*-stream` functions receive
a file descriptor instead of a Lisp stream,
they unconditionally use socket BIO.

### Customize Shared Libraries Location

By default cl+ssl searches for OpenSSL shared libraries
in platform-dependent default locations.

To explicitly specify what to load use cl+ssl/config
module before loading cl+ssl:

```common-lisp

    (ql:quickload :cl+ssl/config)
    (cl+ssl/config:define-libssl-path "/opt/local/lib/libssl.dylib")
    (cl+ssl/config:define-libcrypto-path "/opt/local/lib/libcrypto.dylib")
    (ql:quickload :cl+ssl)

```

Note, the `path` parameter of those two macros is not evaluated.
You can only use literal values. This is dictated by CFFI.

### Timeouts and Deadlines

In network communications it is desirable to be able to interrupt
reading or writing if their duration exceeds some limit.

For example, when making an HTTP request, if it is stuck,
we want to interrupt it instead of leaving the thread hanging
forever. Similarly, a server can encourage some very slow
or stuck clients, who do not timely send their requests or
read responses, and keep connection, and possibly a connection
handling thread, occupied. We want to interrupt server handling
for such clients.

In the description below, by deadline we mean an absolute time,
by which all IO operations have to be completed. And by timeout
we mean longest duration every individual IO operation should
resume in (or at least have some progress).

For example:

```common-lisp

    (json-parser:read-object gzipped-chunked-tls-stream)

```

Such a call can internally perform many primitive IO
operations like `cl:read-byte` or `cl:read-sequence`.
If executed with IO timeouts configured, every individual
operation can take less then the the timeout, but overall
duration may still be unpredictable. In contrast, when
executed with deadline configured, the overall duration
is constrained by the deadline.

Some lisp implementations have implementation-specific ways
to set timeouts or deadlines for socket communications.

For example, on SBCL:

```common-lisp

    (with-deadline (:seconds 3)
        (write-string "something" socket-stream)
        (read-line socket-stream)
        ...
        )

```

On CCL:

```common-lisp

    (setf (ccl:stream-deadline socket-stream)
          (+ (get-internal-real-time)
             (* 3 internal-time-units-per-second))
    (write-string "something" socket-stream)
    (read-line socket-stream)
    ...
    (setf (ccl:stream-deadline socket-stream) nil)

;; or

    (setf (ccl:stream-intput-timeout socket-stream) 3
          (ccl:stream-output-timeout socket-stream) 3)
    (write-string "somemthig" socket-stream)
    (read-line socket-stream)
    ...

```

In the examples, if time runs out, the current IO operation
will be interrupted by signalling an implementation-specific
error.

When using cl+ssl with LispBIO, such implementation-specific
features remain working. You configure timeout / deadline
in implementation-specific way (through the stream as on CCL
or globally as on SBCL) and LispBIO, when performing
standard CL IO functions, receives an error.

BIO captures the error condition, and returns an error
status to OpenSSL. Also BIO saves the error info in OpenSSL
error queue (tries at least).

OpenSSL returns an error status to cl+ssl stream code,
which signals an error condition (a subtype of `cl+ssl::ssl-error`)
to the application code.

```

    Application
    (cl:read-line ssl-stream)   ^  error
    -------------------------   |
                             -->
    cl+ssl::ssl-stream
                                ^  return -1
    -------------------------   |
                             -->
    OpenSSL native code
                                ^  return -1
    -------------------------   |
                             -->
    Lisp BIO
                                ^  ccl:deadline-timeout
    --------------------------  |
                             -->
    (cl:read-sequence socket-stream)

```

Note, in the original design of cl+ssl the error signaled
in the BIO code by standard Lisp IO function was not captured
by BIO, but instead it was passed through to the application
code, so the app saw the implementation specific condition.

```

    Application            ^  ccl:deadline-timeout
    ---------------------  |
    cl+ssl stream          |
    ---------------------  |
    OpenSSL native code    |
    ---------------------  |
    Lisp BIO            -->

```

But in this case, the non-local exit goes across C call stack
of the OpenSSL native code, likely preventing proper stack
cleanup. CFFI manual explicitly advises against that.

That's why BIO handles the timeout error.

For the future we consider changing the behavior to
save the original timeout error condition, let the C stack
unwind normally through error codes, but then resignaling the
the saved error, instead of a cl+ssl defined condition.
That will be closer to the old cl+ssl behavior.
Although not sure if that's really the best approach.

In any case, expect an error to be signaled if your
implementation can arrange for timeout / deadline error
on the socket stream.

Note, such implementation extensions
do not always work reliably, for example
<https://groups.google.com/g/sbcl-devel/c/-eLw-Wv3Prc>.

In case of socket BIO, cl+ssl emulates on CCL and SBCL
the behavior of plain socket streams on these implementations:
it will signal `ccl::communication-deadline-expired` or
`sb-sys:deadline-timeout`. (This is implemented by setting
a non-block flag on the socket file descriptor so that
SSL_Read / SSL_Write only transfer as many data as
possible without blocking. Then cl+ssl waits
for file descriptor to be ready for more IO,
making sure the waiting is no longer than the implementation
specific deadline. In case of CCL the deadline is taken from
the stream originally passed to `cl+ssl:make-client / -server-stream`,
from which the socket file descriptor was extracted. In
case of SBCL the waiting operation used is aware of the global
deadline).

For other Lisp implementations deadlines are not currently
supported in the socket BIO mode.

There are tickets / pull requests open to implement
deadlines or timeouts for socket BIO in all implementations:
[#146](https://github.com/cl-plus-ssl/cl-plus-ssl/issues/146)
[#69](https://github.com/cl-plus-ssl/cl-plus-ssl/pull/69)

One more idea for timeout implementation is to set
socket option SO_RCVTIMEO and SO_SNDTIMEO
for the TCP socket. OpenSSL will probably respect
those options. But that is not tested. (Even if
supported by OpenSSL, we may have problems, for example,
because on several Lisps the socket file descriptor
is used in non-blocking mode; if OpenSSL functions
signall the sockopt timeout by returning
SSL_ERROR_WANT_READ / SSL_ERROR_WANT_WRITE,
cl+ssl code will simply repeat the function call.)

### Saved Lisp Image

If you save your application as a Lisp image, call `(cl+ssl:reload)`
when that image is loaded to make sure necessary re-initialization
is performed.

This should work fine if the location and version
of the OpenSSL shared libraries have *not* changed.
If they have changed, you may get errors,
as users report:
[#167](https://github.com/cl-plus-ssl/cl-plus-ssl/issues/167)

## Portability

CL+SSL requires CFFI with callback support.

CL Test Grid results: <https://common-lisp.net/project/cl-test-grid/library/cl+ssl.html> 


## TODO

- session caching (what about it?)
- The FFI code for all platforms except clisp needs to be rewritten. (update 2017-07-05: does it? why?)


## History

This library is a fork of [SSL-CMUCL](http://www.cliki.net/SSL-CMUCL).
The original SSL-CMUCL source code was written by Eric Marsden and
includes contributions by Jochen Schmidt.

Jochen Schmidt also has his own portable CL-SSL bindings (Gray streams
based), [available]( https://sourceforge.net/p/portableaserve/git/ci/master/tree/acl-compat/)
as a part of the acl-compat portability layer of his
[http://portableaserve.sourceforge.net/](http://portableaserve.sourceforge.net/).

Development into CL+SSL was done by David Lichteblau. After that many
people contributed patches, as can be seen in the git history.


## News (Old, not really maintained now)

2017-07-03

- Hostname verification added, thanks to Ilya Khaprov. Default mode for make-ssl-client-stream is to verify the connection. New keywrd argument verify is added to make-ssl-client-stream with the same possible values as Drakma uses for http request verification.

201?-??-??

- See commits.

2011-05-22

- Added new public function RANDOM-BYTES.

2011-05-22

- The source code repository is moved to Git.

2011-03-25

- OpenSSL libraries names for OpenBSD, thanks to Thomas de Grivel.

2010-05-26

- Fixed two bugs in LISTEN, thanks to Ron Garret.

2009-09-17

- libssl loading on FreeBSD 7.2 fixed, thanks to Stian Sletner.

2008-xx-yy

- Support for I/O deadlines (Clozure CL and SBCL).
- Support for encrypted keys, thanks to Vsevolod Dyomkin.
- Chained certificates support, thanks to Juhani Ränkimies.
- More secure initialization of OpenSSL random number generator.
- Minor CLISP-specific fixes.

2007-xx-yy

- Fixed windows support, thanks to Matthew Kennedy and Anton Vodonosov.

2007-07-07

- Improved CLISP support, thanks to [Pixel // pinterface](http://web.kepibu.org/code/lisp/cl+ssl/), as well as client certificate support.
- Re-introduced support for direct access to file descriptors as an optimization. New function stream-fd. New keyword argument close-callback.

2007-01-16: CL+SSL is now available under an MIT-style license.
