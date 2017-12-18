;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

(in-package :cl+ssl)

(define-condition hostname-verification-error (error)
  ())

(define-condition unable-to-match-altnames (hostname-verification-error)
  ())

(define-condition unable-to-decode-common-name (hostname-verification-error)
  ())

(define-condition unable-to-match-common-name (hostname-verification-error)
  ())

(defun case-insensitive-match (name hostname)
  (string-equal name hostname))

(defun remove-trailing-dot (string)
  (string-right-trim '(#\.) string))

(defun check-wildcard-in-leftmost-label (identifier wildcard-pos)
  (alexandria:when-let ((dot-pos (position #\. identifier)))
    (> dot-pos wildcard-pos)))

(defun check-single-wildcard (identifier wildcard-pos)
  (not (find #\* identifier :start (1+ wildcard-pos))))

(defun check-two-labels-after-wildcard (after-wildcard)
  ;;at least two dots(in fact labels since we remove trailing dot first) after wildcard
  (alexandria:when-let ((first-dot-aw-pos (position #\. after-wildcard)))
    (and (find #\. after-wildcard :start (1+ first-dot-aw-pos))
         first-dot-aw-pos)))

(defun validate-and-parse-wildcard-identifier (identifier hostname)
  (alexandria:when-let ((wildcard-pos (position #\* identifier)))
    (when (and (>= (length hostname) (length identifier)) ;; wildcard should constiute at least one character
               (check-wildcard-in-leftmost-label identifier wildcard-pos)
               (check-single-wildcard identifier wildcard-pos))
      (let ((after-wildcard (subseq identifier (1+ wildcard-pos)))
            (before-wildcard (subseq identifier 0 wildcard-pos)))
        (alexandria:when-let ((first-dot-aw-pos (check-two-labels-after-wildcard after-wildcard)))
          (if (and (= 0 (length before-wildcard))     ;; nothing before wildcard
                   (= wildcard-pos first-dot-aw-pos)) ;; i.e. dot follows *
              (values t before-wildcard after-wildcard t)
              (values t before-wildcard after-wildcard nil)))))))

(defun wildcard-not-in-a-label (before-wildcard after-wildcard)
  (let ((after-w-dot-pos (position #\. after-wildcard)))
    (and
     (not (search "xn--" before-wildcard))
     (not (search "xn--" (subseq after-wildcard 0 after-w-dot-pos))))))

(defun try-match-wildcard (before-wildcard after-wildcard single-char-wildcard pattern)
  ;; Compare AfterW part with end of pattern with length (length AfterW)
  ;; was Wildcard the only character in left-most label in identifier
  ;; doesn't matter since parts after Wildcard should match unconditionally.
  ;; However if Wildcard was the only character in left-most label we can't match this *.example.com and bar.foo.example.com
  ;; if i'm correct if it wasn't the only character
  ;; we can match like this: *o.example.com = bar.foo.example.com
  ;; but this is prohibited anyway thanks to check-vildcard-in-leftmost-label
  (if single-char-wildcard
      (let ((pattern-except-left-most-label
             (alexandria:if-let ((first-hostname-dot-post (position #\. pattern)))
               (subseq pattern first-hostname-dot-post)
               pattern)))
        (case-insensitive-match after-wildcard pattern-except-left-most-label))
      (when (wildcard-not-in-a-label before-wildcard after-wildcard)
        ;; baz*.example.net and *baz.example.net and b*z.example.net would
        ;; be taken to match baz1.example.net and foobaz.example.net and
        ;; buzz.example.net, respectively
        (and
         (case-insensitive-match before-wildcard (subseq pattern 0 (length before-wildcard)))
         (case-insensitive-match after-wildcard (subseq pattern
                                                        (- (length pattern)
                                                           (length after-wildcard))))))))

(defun maybe-try-match-wildcard (name hostname)
  (multiple-value-bind (valid before-wildcard after-wildcard single-char-wildcard)
      (validate-and-parse-wildcard-identifier name hostname)
    (when valid
      (try-match-wildcard before-wildcard after-wildcard single-char-wildcard hostname))))

(defun try-match-hostname (name hostname)
  (let ((name (remove-trailing-dot name))
        (hostname (remove-trailing-dot hostname)))
    (or (case-insensitive-match name hostname)
        (maybe-try-match-wildcard name hostname))))

(defun try-match-hostnames (names hostname)
  (loop for name in names
        when (try-match-hostname name hostname) do
           (return t)))

(defun maybe-check-subject-cn (dns-names cert hostname)
  (when dns-names
    (error 'unable-to-match-altnames))
  ;; TODO: we are matching only first CN
  (alexandria:if-let ((cn (first (certificate-subject-common-names cert))))
    (progn
      (or (try-match-hostname cn hostname)
          (error 'unable-to-match-common-name)))
    (error 'unable-to-decode-common-name)))

(defun verify-hostname (cert hostname)
  (let* ((dns-names (certificate-dns-alt-names cert)))
    (or (try-match-hostnames dns-names hostname)
        (maybe-check-subject-cn dns-names cert hostname))))
