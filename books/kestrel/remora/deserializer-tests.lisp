; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "deserializer")

(include-book "kestrel/json/top" :dir :system)
(include-book "kestrel/json-parser/parse-json" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Deserializer tests.
;;
;; Each test decodes JSON text in the format that [impl]'s Serializer.hs
;; writes.  The text is written with ACL2's #{"""..."""} string syntax,
;; which has no escapes, so [impl]'s output can be pasted in unchanged.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parse STRING as JSON text and convert the result to a json::value.
(define json-string-to-value ((string stringp))
  :returns (mv erp (value json::valuep))
  (b* (((mv erp parsed) (acl2::parse-string-as-json string))
       ((when erp) (mv erp (json::value-null)))
       ((mv erp value) (json::parsed-to-value parsed))
       ((when erp) (mv erp (json::value-null))))
    (mv nil value)))

;; Check that DECODER, one of the X-fromJSON functions, decodes the JSON text
;; JSON-STRING in MODE to EXPECTED.
(defmacro test-fromJSON (decoder json-string mode expected)
  `(assert-event
    (b* (((mv erp value) (json-string-to-value ,json-string))
         ((when erp) (cw "~%Not JSON text: ~x0~%" erp))
         ((mv erp x) (,decoder value ,mode))
         ((when erp) (cw "~%~x0 failed: ~@1~%" ',decoder erp)))
      (or (equal x ,expected)
          (cw "~%~x0 gave ~x1~%  instead of ~x2~%" ',decoder x ,expected)))))

;; Check that DECODER rejects the JSON text JSON-STRING in MODE.
(defmacro test-fromJSON-error (decoder json-string mode)
  `(assert-event
    (b* (((mv erp value) (json-string-to-value ,json-string))
         ((when erp) (cw "~%Not JSON text: ~x0~%" erp))
         ((mv erp x) (,decoder value ,mode)))
      (or erp
          (cw "~%~x0 gave ~x1~%  instead of an error~%" ',decoder x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; TEForall.
;;
;; In [impl]'s ASTs, the parameters of TEForall are TypeParamExps
;; (TEAtomTypeParam or TEArrayTypeParam) before and after uniquification.
;; Only the tp positions change, from TypeParamExp to TypeParam
;; (AtomTypeParam): the parameter of TLambda, the variable of BindType, and
;; the parameters of BindTFun.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (Forall (&t) &t) as [impl] writes it before uniquification
;; (remora dev -p -j), with names as strings.
(defconst *forall-parsed*
  #{"""{"tag": "TEForall",
 "params": [{"tag": "TEAtomTypeParam", "name": "t"}],
 "body": {"tag": "TEAtomVar", "name": "t"}}"""})

;; The same type after uniquification (remora dev -u -j), with names as
;; VNames.
(defconst *forall-unique*
  #{"""{"tag": "TEForall",
 "params": [{"tag": "TEAtomTypeParam",
             "name": {"tag": "VName", "varName": "t",
                      "varTag": {"tag": "Tag", "getTag": 147}}}],
 "body": {"tag": "TEAtomVar",
          "name": {"tag": "VName", "varName": "t",
                   "varTag": {"tag": "Tag", "getTag": 147}}}}"""})

;; Like *forall-unique*, but with the tag of a TypeParam, which [impl] never
;; writes in a TEForall.
(defconst *forall-unique-atom-type-param*
  #{"""{"tag": "TEForall",
 "params": [{"tag": "AtomTypeParam",
             "name": {"tag": "VName", "varName": "t",
                      "varTag": {"tag": "Tag", "getTag": 147}}}],
 "body": {"tag": "TEAtomVar",
          "name": {"tag": "VName", "varName": "t",
                   "varTag": {"tag": "Tag", "getTag": 147}}}}"""})

(test-fromJSON type-fromJSON *forall-parsed* (ast-mode-unchecked)
               (make-type-forall
                :param (make-type-var-atom :name "t")
                :body (make-type-var :var (make-type-var-atom :name "t"))))

(test-fromJSON type-fromJSON *forall-unique* (ast-mode-unique)
               (make-type-forall
                :param (make-type-var-atom :name "t_147")
                :body (make-type-var :var (make-type-var-atom :name "t_147"))))

;; The names in a TEForall are still decoded according to the mode.
(test-fromJSON-error type-fromJSON *forall-unique* (ast-mode-unchecked))

(test-fromJSON-error type-fromJSON *forall-unique-atom-type-param*
                     (ast-mode-unique))

;; The output of remora dev -u -j for this program:
;;
;;   (entry (main (g (Forall (&t) (-> &t &t)))) 0)
(defconst *forall-program-unique*
  #{"""{
    "progDecs": [
        {
            "expr": {
                "atoms": [
                    {
                        "info": null,
                        "lit": {
                            "lit": 0,
                            "tag": "IntVal"
                        },
                        "tag": "Base"
                    }
                ],
                "dims": [],
                "info": null,
                "tag": "Array"
            },
            "info": null,
            "params": [
                {
                    "info": null,
                    "tag": "PatId",
                    "type": {
                        "body": {
                            "in": {
                                "name": {
                                    "tag": "VName",
                                    "varName": "t",
                                    "varTag": {
                                        "getTag": 147,
                                        "tag": "Tag"
                                    }
                                },
                                "tag": "TEAtomVar"
                            },
                            "out": {
                                "name": {
                                    "tag": "VName",
                                    "varName": "t",
                                    "varTag": {
                                        "getTag": 147,
                                        "tag": "Tag"
                                    }
                                },
                                "tag": "TEAtomVar"
                            },
                            "tag": "TEArrow"
                        },
                        "params": [
                            {
                                "name": {
                                    "tag": "VName",
                                    "varName": "t",
                                    "varTag": {
                                        "getTag": 147,
                                        "tag": "Tag"
                                    }
                                },
                                "tag": "TEAtomTypeParam"
                            }
                        ],
                        "tag": "TEForall"
                    },
                    "var": {
                        "tag": "VName",
                        "varName": "g",
                        "varTag": {
                            "getTag": 146,
                            "tag": "Tag"
                        }
                    }
                }
            ],
            "tag": "Entry",
            "type": null,
            "var": {
                "tag": "VName",
                "varName": "main",
                "varTag": {
                    "getTag": 148,
                    "tag": "Tag"
                }
            }
        }
    ],
    "tag": "Prog"
}"""})

(test-fromJSON
 file-fromJSON *forall-program-unique* (ast-mode-unique)
 (b* ((var-t (make-type-var :var (make-type-var-atom :name "t_147"))))
   (make-file
    :imports nil
    :decls (list
            (make-decl-entry
             :var "main_148"
             :params (list
                      (make-var+type?
                       :var "g_146"
                       :type? (make-type-option-some
                               :val (make-type-forall
                                     :param (make-type-var-atom :name "t_147")
                                     :body (make-type-fun :in var-t
                                                          :out var-t)))))
             :type? (make-type-option-none)
             :expr (make-expr-array
                    :dims nil
                    :atoms (list
                            (make-atom-base
                             :lit (make-base-lit-int
                                   :lit (make-int-lit :digits '(#\0)))))))))))
