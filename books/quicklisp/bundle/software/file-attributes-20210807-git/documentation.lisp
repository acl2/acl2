#|
 This file is a part of file-attributes
 (c) 2020 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(in-package #:org.shirakumo.file-attributes)

(docs:define-docs
  (function access-time
    "Accesses the last time this file was accessed.

Signals an error if retrieving or setting the information is not
possible.")
  
  (function modification-time
    "Accesses the last time this file was modified.

Signals an error if retrieving or setting the information is not
possible.")
  
  (function creation-time
    "Accesses the time this file was created.

Signals an error if retrieving or setting the information is not
possible.")
  
  (function group
    "Accesses the owning group of this file.

The group is expressed as a positive integer.

Signals an error if retrieving or setting the information is not
possible.")
  
  (function owner
    "Accesses the owning user of this file.

The user is expressed as a positive integer.

Signals an error if retrieving or setting the information is not
possible.")
  
  (function attributes
    "Accesses the attributes of this file.

The attributes are expressed as a positive integer.

Signals an error if retrieving or setting the information is not
possible.

The contents of the file attributes are highly system specific and may
contain things such as user permissions or file kind information.

See ENCODE-ATTRIBUTES
See DECODE-ATTRIBUTES")

  (variable *system*
    "The default system as recognised through feature flags.")

  (function encode-attributes
    "Encodes a plist of file attributes into an integer suitable for the requested system.

See DECODE-ATTRIBUTES
See *SYSTEM*")

  (function decode-attributes
    "Decodes an integer for attributes of the requested system into a standardised plist of file attributes.

Which flags are be produced is highly dependent on the system, but the
following may appear:

  :ARCHIVED
  :COMPRESSED
  :DEVICE
  :DIRECTORY
  :ENCRYPTED
  :FIFO
  :GROUP-EXECUTE
  :GROUP-READ
  :GROUP-WRITE
  :HIDDEN
  :INTEGRITY
  :LINK
  :NO-SCRUB
  :NORMAL
  :NOT-INDEXED
  :OFFLINE
  :OTHER-EXECUTE
  :OTHER-READ
  :OTHER-WRITE
  :OWNER-EXECUTE
  :OWNER-READ
  :OWNER-WRITE
  :READ-ONLY
  :RECALL
  :SET-GROUP
  :SET-USER
  :SOCKET
  :SPARSE
  :STICKY
  :SYSTEM-FILE
  :TEMPORARY
  :VIRTUAL

See ENCODE-ATTRIBUTES
See *SYSTEM*"))

