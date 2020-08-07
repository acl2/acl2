;;;; -*- Mode: lisp; indent-tabs-mode: nil -*-
;;;
;;; enc-cp437.lisp --- Implementation of the IBM Code Page 437
;;;
;;; Copyright (C) 2020, Nicolas Hafner  <shinmera@tymoon.eu>
;;;
;;; Permission is hereby granted, free of charge, to any person
;;; obtaining a copy of this software and associated documentation
;;; files (the "Software"), to deal in the Software without
;;; restriction, including without limitation the rights to use, copy,
;;; modify, merge, publish, distribute, sublicense, and/or sell copies
;;; of the Software, and to permit persons to whom the Software is
;;; furnished to do so, subject to the following conditions:
;;;
;;; The above copyright notice and this permission notice shall be
;;; included in all copies or substantial portions of the Software.
;;;
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;; NONINFRINGEMENT.  IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;; WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;; DEALINGS IN THE SOFTWARE.

(in-package #:babel-encodings)

(define-character-encoding :cp437
    "An 8-bit, fixed-width character encoding from IBM."
  :aliases '(:oem-us :oem-437 :pc-8 :dos-latin-us)
  :literal-char-code-limit #xFF)

(define-constant +cp437-to-unicode+
    #(#x0000 #x0001 #x0002 #x0003 #x0004 #x0005 #x0006 #x0007
      #x0008 #x0009 #x000a #x000b #x000c #x000d #x000e #x000f
      #x0010 #x0011 #x0012 #x0013 #x0014 #x0015 #x0016 #x0017
      #x0018 #x0019 #x001a #x001b #x001c #x001d #x001e #x001f
      #x0020 #x0021 #x0022 #x0023 #x0024 #x0025 #x0026 #x0027
      #x0028 #x0029 #x002a #x002b #x002c #x002d #x002e #x002f
      #x0030 #x0031 #x0032 #x0033 #x0034 #x0035 #x0036 #x0037
      #x0038 #x0039 #x003a #x003b #x003c #x003d #x003e #x003f
      #x0040 #x0041 #x0042 #x0043 #x0044 #x0045 #x0046 #x0047
      #x0048 #x0049 #x004a #x004b #x004c #x004d #x004e #x004f
      #x0050 #x0051 #x0052 #x0053 #x0054 #x0055 #x0056 #x0057
      #x0058 #x0059 #x005a #x005b #x005c #x005d #x005e #x005f
      #x0060 #x0061 #x0062 #x0063 #x0064 #x0065 #x0066 #x0067
      #x0068 #x0069 #x006a #x006b #x006c #x006d #x006e #x006f
      #x0070 #x0071 #x0072 #x0073 #x0074 #x0075 #x0076 #x0077
      #x0078 #x0079 #x007a #x007b #x007c #x007d #x007e #x007f
      #x00c7 #x00fc #x00e9 #x00e2 #x00e4 #x00e0 #x00e5 #x00e7
      #x00ea #x00eb #x00e8 #x00ef #x00ee #x00ec #x00c4 #x00c5
      #x00c9 #x00e6 #x00c6 #x00f4 #x00f6 #x00f2 #x00fb #x00f9
      #x00ff #x00d6 #x00dc #x00a2 #x00a3 #x00a5 #x20a7 #x0192
      #x00e1 #x00ed #x00f3 #x00fa #x00f1 #x00d1 #x00aa #x00ba
      #x00bf #x2310 #x00ac #x00bd #x00bc #x00a1 #x00ab #x00bb
      #x2591 #x2592 #x2593 #x2502 #x2524 #x2561 #x2562 #x2556
      #x2555 #x2563 #x2551 #x2557 #x255d #x255c #x255b #x2510
      #x2514 #x2534 #x252c #x251c #x2500 #x253c #x255e #x255f
      #x255a #x2554 #x2569 #x2566 #x2560 #x2550 #x256c #x2567
      #x2568 #x2564 #x2565 #x2559 #x2558 #x2552 #x2553 #x256b
      #x256a #x2518 #x250c #x2588 #x2584 #x258c #x2590 #x2580
      #x03b1 #x00df #x0393 #x03c0 #x03a3 #x03c3 #x00b5 #x03c4
      #x03a6 #x0398 #x03a9 #x03b4 #x221e #x03c6 #x03b5 #x2229
      #x2261 #x00b1 #x2265 #x2264 #x2320 #x2321 #x00f7 #x2248
      #x00b0 #x2219 #x00b7 #x221a #x207f #x00b2 #x25a0 #x00a0)
  :test #'equalp)

(define-unibyte-decoder :cp437 (octet)
  (svref +cp437-to-unicode+ octet))

(define-unibyte-encoder :cp437 (code)
  (if (<= code 127)
      code
      ;; Adjacent code point groups are too small and too many to be
      ;; worth tabulating this, so we just use a case.
      (case code
        (#x7F #x7F)
        (#xA0 #x80)
        (#xA1 #x81)
        (#xA2 #x82)
        (#xA3 #x83)
        (#xA5 #x84)
        (#xAA #x85)
        (#xAB #x86)
        (#xAC #x87)
        (#xB0 #x88)
        (#xB1 #x89)
        (#xB2 #x8A)
        (#xB5 #x8B)
        (#xB7 #x8C)
        (#xBA #x8D)
        (#xBB #x8E)
        (#xBC #x8F)
        (#xBD #x90)
        (#xBF #x91)
        (#xC4 #x92)
        (#xC5 #x93)
        (#xC6 #x94)
        (#xC7 #x95)
        (#xC9 #x96)
        (#xD1 #x97)
        (#xD6 #x98)
        (#xDC #x99)
        (#xDF #x9A)
        (#xE0 #x9B)
        (#xE1 #x9C)
        (#xE2 #x9D)
        (#xE4 #x9E)
        (#xE5 #x9F)
        (#xE6 #xA0)
        (#xE7 #xA1)
        (#xE8 #xA2)
        (#xE9 #xA3)
        (#xEA #xA4)
        (#xEB #xA5)
        (#xEC #xA6)
        (#xED #xA7)
        (#xEE #xA8)
        (#xEF #xA9)
        (#xF1 #xAA)
        (#xF2 #xAB)
        (#xF3 #xAC)
        (#xF4 #xAD)
        (#xF6 #xAE)
        (#xF7 #xAF)
        (#xF9 #xB0)
        (#xFA #xB1)
        (#xFB #xB2)
        (#xFC #xB3)
        (#xFF #xB4)
        (#x192 #xB5)
        (#x393 #xB6)
        (#x398 #xB7)
        (#x3A3 #xB8)
        (#x3A6 #xB9)
        (#x3A9 #xBA)
        (#x3B1 #xBB)
        (#x3B4 #xBC)
        (#x3B5 #xBD)
        (#x3C0 #xBE)
        (#x3C3 #xBF)
        (#x3C4 #xC0)
        (#x3C6 #xC1)
        (#x207F #xC2)
        (#x20A7 #xC3)
        (#x2219 #xC4)
        (#x221A #xC5)
        (#x221E #xC6)
        (#x2229 #xC7)
        (#x2248 #xC8)
        (#x2261 #xC9)
        (#x2264 #xCA)
        (#x2265 #xCB)
        (#x2310 #xCC)
        (#x2320 #xCD)
        (#x2321 #xCE)
        (#x2500 #xCF)
        (#x2502 #xD0)
        (#x250C #xD1)
        (#x2510 #xD2)
        (#x2514 #xD3)
        (#x2518 #xD4)
        (#x251C #xD5)
        (#x2524 #xD6)
        (#x252C #xD7)
        (#x2534 #xD8)
        (#x253C #xD9)
        (#x2550 #xDA)
        (#x2551 #xDB)
        (#x2552 #xDC)
        (#x2553 #xDD)
        (#x2554 #xDE)
        (#x2555 #xDF)
        (#x2556 #xE0)
        (#x2557 #xE1)
        (#x2558 #xE2)
        (#x2559 #xE3)
        (#x255A #xE4)
        (#x255B #xE5)
        (#x255C #xE6)
        (#x255D #xE7)
        (#x255E #xE8)
        (#x255F #xE9)
        (#x2560 #xEA)
        (#x2561 #xEB)
        (#x2562 #xEC)
        (#x2563 #xED)
        (#x2564 #xEE)
        (#x2565 #xEF)
        (#x2566 #xF0)
        (#x2567 #xF1)
        (#x2568 #xF2)
        (#x2569 #xF3)
        (#x256A #xF4)
        (#x256B #xF5)
        (#x256C #xF6)
        (#x2580 #xF7)
        (#x2584 #xF8)
        (#x2588 #xF9)
        (#x258C #xFA)
        (#x2590 #xFB)
        (#x2591 #xFC)
        (#x2592 #xFD)
        (#x2593 #xFE)
        (#x25A0 #xFF)
        (t (handle-error)))))
