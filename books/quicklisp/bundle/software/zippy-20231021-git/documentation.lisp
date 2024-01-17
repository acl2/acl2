(in-package #:org.shirakumo.zippy)

;; compression.lisp
(docs:define-docs
  (function make-decompression-state
    "Create the state necessary to decompress given the requested compression format.

If required, the supplied buffer spec should be used to create the
output buffer for the decompression. The buffer spec may be either NIL
for a default buffer, an octet vector, or an integer for an octet
vector of the given size.

See CALL-WITH-DECOMPRESSED-BUFFER")

  (function call-with-decompressed-buffer
    "Call the supplied function with a decompressed buffer.

The function is called with three arguments:
  An octet buffer with the decompressed data
  A start index to the beginning of valid data
  An end index to the end of valid data
It must return an integer indicating the last index that was consumed
in the octet buffer. If the index is the same as START, DECODE-ENTRY
will return.

The supplied STATE must be a state obtained through
MAKE-DECOMPRESSION-STATE. The VECTOR, START, and END supply the octets
to decompress.

You may call this function repeatedly with new input to decompress
until the full region has been processed. The supplied function
likewise may be called multiple times per decompression run.

This function returns how much of the supplied buffer has been
consumed. If the function return START, it should not be called
again until external circumstances allow the inner function to
continue.

See MAKE-DECOMPRESSION-STATE")

  (function make-compression-state
    "Create the state necessary to compress given the requested compression format.

If required, the supplied buffer spec should be used to create the
output buffer for the compression. The buffer spec may be either NIL
for a default buffer, an octet vector, or an integer for an octet
vector of the given size.

See CALL-WITH-COMPRESSED-BUFFER
See CALL-WITH-COMPLETED-COMPRESSED-BUFFER")

  (function call-with-compressed-buffer
    "Call the supplied function with a compressed buffer.

The function is called with three arguments:
  An octet buffer with the compressed data
  A start index to the beginning of valid data
  An end index to the end of valid data

The supplied STATE must be a state obtained through
MAKE-COMPRESSION-STATE. The VECTOR, START, and END supply the octets
to compress.

You may call this function repeatedly with new input to compress
until the full region has been processed. The supplied function
likewise may be called multiple times per compression run.

See MAKE-COMPRESSION-STATE
See CALL-WITH-COMPLETED-COMPRESSED-BUFFER")

  (function call-with-completed-compressed-buffer
    "Finishes the compression and calls the function with tail data.

The function is called with three arguments:
  An octet buffer with the compressed data
  A start index to the beginning of valid data
  An end index to the end of valid data

The supplied STATE must be a state obtained through
MAKE-COMPRESSION-STATE. The VECTOR, START, and END supply the octets
to compress.

You must call this function only once, after all data has been
processed via CALL-WITH-COMPRESSED-BUFFER. Further calls to
CALL-WITH-COMPRESSED-BUFFER after this function has been called are
illegal.

See MAKE-COMPRESSION-STATE
See CALL-WITH-COMPRESSED-BUFFER"))

;; decode.lisp
(docs:define-docs
  (type archive-file-required
    "Condition signalled if data from another disk (split file) is required.

When this condition is signalled, a USE-VALUE restart must be
available. If invoked, the value must be an IO value that supplies the
data of the requested DISK.

See DISK
See DECODE-FILE
See DECODE-ENTRY")

  (function with-zip-file
    "Open a zip file lexically and cleans up on exit.

If decoding is successful, FILE will be bound to the resulting
ZIP-FILE instance. This instance is only valid within BODY. After
leaving the BODY, you may still access metadata and zip entries, but
you may not use DECODE-ENTRY to extract an entry's payload.

See DECODE-ENTRY
See DECODE-FILE
See OPEN-ZIP-FILE")

  (function decode-file
    "Decode the given IO into a ZIP-FILE.

If the zip file is split, will signal a condition of type
ARCHIVE-FILE-REQUIRED for every disk that is required to read the
central directory of the zip file.

May signal warnings if data mismatch or other correctable corruption
is detected in the zip file.

May signal an error if an incorrectable corruption is detected in the
zip file, or if the file is missing vital support structures that
would make it a valid zip file.

See WITH-ZIP-FILE
See ARCHIVE-FILE-REQUIRED")

  (function open-zip-file
    "Opens a zip file and parses its directory.

Returns two values if successful:
  The new ZIP-FILE that was parsed
  A list of streams that were opened

After closing the streams the ZIP-FILE contents cannot be extracted,
so you must take care to close them at the opportune time
yourself. For a lexical variant of this, see WITH-ZIP-FILE.

INPUT may be a pathname or string to designate a local file, a
seekable stream to read from, or an octet-vector to decode.

If the zip file is split and the supplied INPUT is a pathname
designator, other split disks will be determined automatically by
using the same pathname, but substituting the pathname-type by the
scheme z{DISK} . If INPUT is not a pathname designator, a condition of
type ARCHIVE-FILE-REQUIRED is signalled for every split disk that is
required, for which you should invoke the USE-VALUE restart with the
newly opened stream.

See ZIP-FILE
See DECODE-FILE
See DECODE-ENTRY
See ARCHIVE-FILE-REQUIRED
See WITH-ZIP-FILE")

  (function decode-entry
    "Decode the data payload of the ZIP-ENTRY

FUNCTION will be called repeatedly with three arguments:
  An octet buffer with the raw data
  A start index to the beginning of valid data
  An end index to the end of valid data
It must return an integer indicating the last index that was consumed
in the octet buffer. If the index is the same as START, DECODE-ENTRY
will return with a value greater than zero.

PASSWORD should be supplied if the entry is encrypted. If the entry is
encrypted, but no password is supplied, or the password is detectably
incorrect, an error is signalled. The password may be a string or an
octet-vector.

If an error is detected during decoding of the payload, an error is
signalled.

If the zip file is split a condition of type ARCHIVE-FILE-REQUIRED may
be signalled.

See ENTRY-TO-FILE
See ENTRY-TO-STREAM
See ENTRY-TO-VECTOR
See ARCHIVE-FILE-REQUIRED"))

;; toolkit.lisp
(docs:define-docs
  (variable *default-buffer-size*
    "Default buffer size when working on compressed data.

For example this can be bound around calls to DECODE-ENTRY to give a
more accurate size for the temporary buffer being allocated to decode
a particular file.

See DECODE-ENTRY
See ENCODE-FILE
See MAKE-DECRYPTION-STATE
See MAKE-DECOMPRESSION-STATE"))

;; encode.lisp
(docs:define-docs
  (variable *default-version-made*
    "Default archive creation software version to be stored in produced
archives.")

  (variable *default-version-needed*
    "Default required archive reader software version to be stored in
produced archives.")

  (variable *compatibility*
    "The default file attribute compatibility flag.")

  (function encode-file
    "Encodes the given zip-file to the output IO.

This currently does not support split archive creation. All the
entries will be written to the output.

This will cause the ZIP-ENTRIES in the ZIP-FILE to be modified.
In particular, SIZE, CRC-32, and UNCOMPRESSED-SIZE will be set, and
LAST-MODIFIED, FILE-NAME, ATTRIBUTES, and COMPRESSION-METHOD may be
set.

The created Zip file will include Zip64 metadata regardless of whether
this is required, but it will only enforce Zip64 decoding if the
number of entries, or the size of an entry exceeds the possible bounds
of traditional 32-bit zip files.

If an encryption-method is specified for any entry, PASSWORD must be
passed and will be used to encrypt the file.

See ZIP-FILE
See ZIP-ENTRY"))

;; encryption.lisp
(docs:define-docs
  (function make-decryption-state
    "Create the state necessary to decrypt given the requested encryption format.

If required, the supplied buffer spec should be used to create the
output buffer for the decryption. The buffer spec may be either NIL
for a default buffer, an octet vector, or an integer for an octet
vector of the given size.

The given password may be a string or octet vector supplying the
password for decryption.

See CALL-WITH-DECRYPTED-BUFFER")

  (function call-with-decrypted-buffer
    "Call the supplied function with a decrypted buffer.

The function is called with three arguments:
  An octet buffer with the decrypted data
  A start index to the beginning of valid data
  An end index to the end of valid data
It must return an integer indicating the last index that was consumed
in the octet buffer. If the index is the same as START, DECODE-ENTRY
will return.

The supplied STATE must be a state obtained through
MAKE-DECRPTIION-STATE. The VECTOR, START, and END supply the octets
to decrypt.

You may call this function repeatedly with new input to decrypt
until the full region has been processed. The supplied function
likewise may be called multiple times per decryption run.

This function returns how much of the supplied buffer has been
consumed. If the function return START, it should not be called
again until external circumstances allow the inner function to
continue.

See MAKE-DECRYPTION-STATE")

  (function make-encryption-state
    "Create the state necessary to encrypt given the requested encryption format.

If required, the supplied buffer spec should be used to create the
output buffer for the encryption. The buffer spec may be either NIL
for a default buffer, an octet vector, or an integer for an octet
vector of the given size.

See CALL-WITH-ENCRYPTED-BUFFER
See CALL-WITH-COMPLETED-ENCRYPTED-BUFFER")

  (function call-with-encrypted-buffer
    "Call the supplied function with an encrypted buffer.

The function is called with three arguments:
  An octet buffer with the encrypted data
  A start index to the beginning of valid data
  An end index to the end of valid data

The supplied STATE must be a state obtained through
MAKE-ENCRYPTION-STATE. The VECTOR, START, and END supply the octets
to encrypt.

You may call this function repeatedly with new input to encrypt
until the full region has been processed. The supplied function
likewise may be called multiple times per encryption run.

See MAKE-ENCRYPTION-STATE
See CALL-WITH-COMPLETED-ENCRYPTED-BUFFER")

  (function call-with-completed-encrypted-buffer
    "Finishes the encryption and calls the function with tail data.

The function is called with three arguments:
  An octet buffer with the compressed data
  A start index to the beginning of valid data
  An end index to the end of valid data

The supplied STATE must be a state obtained through
MAKE-ENCRYPTION-STATE. The VECTOR, START, and END supply the octets
to compress.

You must call this function only once, after all data has been
processed via CALL-WITH-ENCRYPTED-BUFFER. Further calls to
CALL-WITH-ENCRYPTED-BUFFER after this function has been called are
illegal.

See MAKE-ENCRYPTION-STATE
See CALL-WITH-ENCRYPTED-BUFFER"))

;; io.lisp
(docs:define-docs
  (type io
    "Type for objects that Zippy can decode from or encode to.

Decoding can only happen from an input with a fixed end and the
ability to seek -- in effect file-streams and vectors.

Encoding can happen to any stream and vector.

See CL:STREAM
See CL:FILE-STREAM
See VECTOR-INPUT
See SEEK
See HAS-MORE
See INDEX
See START
See END
See SIZE
See UB32
See OUTPUT
See PARSE-STRUCTURE*
See WRITE-STRUCTURE*
See PARSE-STRUCTURE
See WITH-IO")

  (type vector-input
    "Representation of vector input/output state.

See VECTOR-INPUT-VECTOR
See VECTOR-INPUT-INDEX
See VECTOR-INPUT-START
See VECTOR-INPUT-END")

  (function vector-input-vector
    "Returns the vector the vector-input is backing.

See VECTOR-INPUT")

  (function vector-input-index
    "Accesses the current index into the vector.

See VECTOR-INPUT")

  (function vector-input-start
    "Returns the starting index of the vector.

See VECTOR-INPUT")

  (function vector-input-end
    "Returns the ending index of the vector.

See VECTOR-INPUT")

  (function seek
    "Seek the io to the requested index.

If the index is outside the allowed ranges, an error is signalled.

See IO")

  (function has-more
    "Returns whether the io has input left to read, or space left to write to.

See IO")

  (function index
    "Returns the current index into the IO.

This should always be in the range of [START, END].

See IO")

  (function start
    "Returns the starting index of the IO.

See IO")

  (function end
    "Returns the ending index of the IO.

See IO")

  (function size
    "Returns the size of the object in octets.

For zip-entries this is the number of octets in compressed format as
they are in the archive.

See ZIP-ENTRY
See IO")

  (function ub32
    "Reads a 32 bit unsigned integer from the IO and returns it.

This will advance the IO index.

See IO")

  (function output
    "Writes the given array of octets to the IO.

If the IO does not have sufficient space available, an error is
signalled.

See IO")

  (function parse-structure*
    "Parses a structure from the IO assuming a leading 32 bit signature.

If no suitable structure can be found, an error is
signalled. Otherwise, the parsed structure instance is returned.

This advances the IO index.

See IO")

  (function write-structure*
    "Writes the given structure to the IO.

This advances the IO index.

See IO")

  (function parse-structure
    "Parse the given structure type from the IO.

This advances the IO index.

See IO")

  (function with-io
    "Wraps TARGET in an appropriate IO context.

TARGET may be a string or pathname, a stream, or a vector. In the case
of a pathname or string, IF-EXISTS and DIRECTION can be passed as
arguments for OPEN. In the case off a vector, START and END may be
passed to designate a sub-range of the vector.

See IO"))

;; parser.lisp
(docs:define-docs
  (function decode-structure
    "Decodes a structure from the given vector at the given starting position.

A signature is expected at the input position. If no signature
is available, or if it is not recognised, an error is signalled.

Returns the structure instance and the ending index.")

  (function read-structure
    "Decodes a structure from the given stream.

A signature is expected at the input position. If no signature
is available, or if it is not recognised, an error is signalled.
Returns the structure instance otherwise.")

  (function encode-structure
    "Encodes the given structure to the vector at the given starting position.

This will encode it including its signature, if any.

Returns the ending index.")

  (function write-structure
    "Encodes the given structure to the stream.

This will encode it including its signature, if any.")

  (function define-byte-structure
    "Define a new byte-coded structure.

NAME can either be the name of the structure, or a list of the name
and the signature that identifies the record uniquely. If a signature
is given, the structure is registered and can be used with the
standard functions DECODE/READ/ENCODE/WRITE-STRUCTURE.

Each RECORD must be a list matching

  (NAME TYPE &optional COUNT)

Where NAME identifies the field, TYPE identifies the name field's bit
type, and COUNT the number of expected entries for a variable sized
record. If COUNT is specified, it may be an arbitrary expression that
can reference earlier record values by name, and the resulting slot
value will be an octet vector of that length.

The special record name SIZE may be used to identify a field that
identifies the maximal size of the remaining structure payload. Any
structure fields that would come after the dynamically read size has
run out will be initialised to NIL.

TYPE may be one of ub8 ub16 ub32 ub64

This will generate a structure of NAME with the given records as
slots, as well as four functions to encode and decode the
structure, and one function to construct it. These functions are
constructed according to the following schema:

  (MAKE/DECODE/READ/ENCODE/WRITE)-NAME

The given function names are interned in the current package.

See DECODE-STRUCTURE
See READ-STRUCTURE
See ENCODE-STRUCTURE
See WRITE-STRUCTURE"))

;; structures.lisp
(docs:define-docs)

;; tables.lisp
(docs:define-docs
  (function file-attribute-name
    "Returns the file attribute name for the given ID.

The name should be one of
  :ms-dos
  :amiga
  :open-vms
  :unix
  :vm/cms
  :atari-st
  :os/2
  :macintosh
  :z-system
  :cp/m
  :ntfs
  :mvs
  :vse
  :acorn-risc
  :vfat
  :alternate-mvs
  :beos
  :tandem
  :os/400
  :darwin

If the ID is not known, an error is signalled.")

  (function file-attribute-id
    "Returns the file attribute ID for the given name.

If The name is not known, an error is signalled.")

  (function compression-method-name
    "Returns the compression method name for the given ID.

The name should be one of
  :store
  :shrink
  :reduce-1
  :reduce-2
  :reduce-3
  :reduce-4
  :implode
  :tokenizing
  :deflate
  :deflate64
  :pkware-implode
  :reserved
  :bzip2
  :reserved
  :lzma
  :reserved
  :cmpsc
  :reserved
  :terse
  :lz77
  :zstd
  :jpeg
  :wavpack
  :ppmd
  :ae-x

If the ID is not known, an error is signalled.")

  (function compression-method-id
    "Returns the compression method ID for the given name.

If The name is not known, an error is signalled.")

  (function encryption-method-name
    "Returns the encryption method name for the given ID.

The name should be one of
  :des
  :rc2
  :3des-168
  :3des-112
  :aes-128
  :aes-192
  :aes-256
  :rc2
  :blowfish
  :twofish
  :rc4
  :unknown

If the ID is not known, an error is signalled.")

  (function encryption-method-id
    "Returns the encryption method ID for the given name.

If The name is not known, an error is signalled."))

;; zippy.lisp
(docs:define-docs
  (type zip-file
    "Representation of a full zip archive.

In order to ensure that all potentially open streams that the zip-file
may hold are closed, call CL:CLOSE.

See ENTRIES
See DISKS
See COMMENT
See DECODE-FILE
See CL:CLOSE")

  (function entries
    "Accessor to the vector of zip-entry instances for the zip-file.

See ZIP-FILE
See ZIP-ENTRY")

  (function disks
    "Accessor to the vector of IO instances representing the zip-file's disks.

This vector is managed automatically.

See ZIP-FILE
See IO")

  (function comment
    "Accessor to the comment of the zip-file or entry.

See ZIP-FILE
See ZIP-ENTRY")

  (function move-in-memory
    "Moves the zip archive into memory. This will be far faster for repeat access and decompression.

Does nothing if the file is already in-memory.
Signals an error if any of the disks are closed streams.

See ZIP-FILE")

  (type zip-entry
    "Representation of a file entry in a zip archive.

Unless you are constructing an archive, this does /not/ contain the
actual entry data payload.

See ZIP-FILE
See CRC-32
See DISK
See OFFSET
see SIZE
See UNCOMPRESSED-SIZE
See EXTRA-FIELDS
See VERSION
See ATTRIBUTES
See ENCRYPTION-METHOD
See COMPRESSION-METHOD
See LAST-MODIFIED
See FILE-NAME
See COMMENT
See CONTENT")

  (function zip-file
    "Returns the zip-file instance this entry is a part of.

See ZIP-ENTRY
See ZIP-FILE")

  (function version
    "Returns the Zip file version needed to extract this entry.

The version is a list of two integers.

This slot should not be set by the user.

See ZIP-ENTRY")

  (function attributes
    "Accesses the file attributes.

This should be a list of three entries, the MSDOS file attribute list,
the compatibility identifier, and the system-specific attributes
encoded as an integer.

For ZIP-ENTRIES that are backed by a file, this entry is computed
automatically when the entry is encoded.

See FILE-ATTRIBUTE-NAME
See ZIP-ENTRY
See ORG.SHIRAKUMO.FILE-ATTRIBUTES:PERMISSIONS")

  (function encryption-method
    "Accesses the encryption method used to encrypt the file contents.

This should either be NIL, a keyword, or a list of a keyword and extra
parameters. The keyword identifies the name of the encryption method.
Additionally to the names listed in ENCRYPTION-METHOD-NAME, the names
:AE-1 and :AE-2 are allowed.

See ENCRYPTION-METHOD-NAME
See ZIP-ENTRY")

  (function compression-method
    "Accesses the compression method used to compress the file
    contents.

This should either be NIL or a keyword naming the compression method.

See COMPRESSION-METHOD-NAME
See ZIP-ENTRY")

  (function crc-32
    "Accesses the CRC-32 checksum of the file contents.

This is computed and set automatically when the entry is encoded.

See ZIP-ENTRY")

  (function disk
    "Accesses the disk ID on which the contents of this file start.

This slot should not be set by the user.

See OFFSET
See ZIP-ENTRY")

  (function offset
    "Accesses the octet index at which the contents of this file start
    on its disk.

This slot should not be set by the user.

See DISK
See ZIP-ENTRY")

  (function uncompressed-size
    "Accesses the octet size of the entry's uncompressed data payload.

If unset, this slot is automatically computed when the entry is
encoded.

See ZIP-ENTRY")

  (function extra-fields
    "Accesses the list of extra data structures for the entry.

This slot should not be set by the user.

See ZIP-ENTRY")

  (function last-modified
    "Accesses the universal time designating the last time the entry's contents were modified.

If unset, and the entry is backed by a file, this slot is
automatically computed when the entry is encoded.

See ZIP-ENTRY")

  (function file-name
    "Accesses the relative path designating where the file belongs on a hirearchical file system.

When the entry is encoded and this slot is unset, it may be computed
automatically if the entry is backed by a file. Otherwise, an error is
signalled.

The path must be relative, and must use forward slashes as the
directory separator.

See ZIP-ENTRY")

  (function content
    "Accesses the backing content of the file.

This slot must be set by the user to a suitable source for the file's
contents. It may be either a string or pathname to designate a file
from disk, an octet input-stream, an octet vector, or an IO instance.

See IO
See ZIP-ENTRY")

  (function entry-to-file
    "Decodes the contents of the entry to the given path.

This will attempt to restore the same file attributes as are contained
in the entry's metadata, unless :RESTORE-ATTRIBUTES NIL is passed.

See DECODE-ENTRY
See CL:OPEN
See ZIP-ENTRY")

  (function entry-to-stream
    "Decodes the contents of the entry to the given octet input-stream.

See DECODE-ENTRY
See ZIP-ENTRY")

  (function entry-to-vector
    "Decodes the contents of the entry to an octet vector.

If an octet vector is passed explicitly through :VECTOR, the vector
must be at least START+(UNCOMPRESSED-SIZE ENTRY) big.

See DECODE-ENTRY
See ZIP-ENTRY")

  (function extract-zip
    "Extracts the contents of the zip file to the given directory.

FILE may either be a ZIP-FILE, or a suitable input for WITH-ZIP-FILE.
PATH should be a directory pathname designator.

See ZIP-FILE
See ENTRY-TO-FILE
See WITH-ZIP-FILE")

  (function compress-zip
    "Compresses the contents of the zip file to the given output.

FILE should be a ZIP-FILE.
TARGET should be a suitable target for WITH-IO.

See WITH-IO
See ENCODE-FILE
See ZIP-FILE"))
