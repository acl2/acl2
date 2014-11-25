/*
; XDOC Documentation System for ACL2
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>
*/

// xslt.js
//
// Compatbility wrapper for lack of XSLT standards in browsers.
//
// Interface:
//   renderText(String of XDOC XML markup) -> String of Plain Text
//   renderHtml(String of XDOC XML markup) -> HTML DOM Object



function wrapXdocFragment(str) {
    var wrap = "<!DOCTYPE xdoc [";
    wrap += "<!ENTITY mdash \"&#8212;\">";
    wrap += "<!ENTITY rarr \"&#8594;\">";
    wrap += "<!ENTITY nbsp \"&#160;\">";
    wrap += "]>";
    wrap += "<root>" + str + "</root>";
    return wrap;
}

var xslt_impl = {};

function xsltInit() {

    if (window.ActiveXObject // detects IE <= version 11
        || "ActiveXObject" in window // detects IE version 11
       )
    {
	var xslt_plain = $.base64.decode(xslt_base64);

	var xsltdom = new ActiveXObject("Msxml2.DOMDocument.6.0");
	xsltdom.validateOnParse = true;
	xsltdom.async = false;
	xsltdom.loadXML(xslt_plain);
	xslt_impl["proc"] = xsltdom;

	var xmldom  = new ActiveXObject("Msxml2.DOMDocument.6.0");
	xmldom.validateOnParse = false;
	xmldom.async = false;
	xmldom.setProperty("ProhibitDTD", false);

	xslt_impl["renderText"] = function(str) {
	    xmldom.loadXML(wrapXdocFragment(str));
	    if (xmldom.parseError.errorCode != 0) {
		var myErr = xmldom.parseError;
		try {
		    console.log("IE XML Error: " + myErr.reason);
		}catch(e) {}
		return "Error: " + myErr.reason;
	    }
	    var output = xmldom.transformNode(xsltdom);
	    var str = $("<div>" + output + "</div>").text();
	    var ret = String(str)
 		       .replace(/"/g, '&quot;')
		       .replace(/'/g, '&apos;');
	    return ret;
	};

	xslt_impl["renderHtml"] = function(str) {
	    xmldom.loadXML(wrapXdocFragment(str));
	    if (xmldom.parseError.errorCode != 0) {
		var myErr = xmldom.parseError;
		try {
		    console.log("IE XML Error: " + myErr.reason);
		}catch(e) {}
		return "Error: " + myErr.reason;
	    }
	    var output = xmldom.transformNode(xsltdom);
	    var str = $("<div>" + output + "</div>");
	    return str;
	};

    }

    else {

	// Initialize an XSLT processor for XDOC --> HTML conversion
	xslt_impl["proc"] = new XSLTProcessor();
	var xslt_plain = $.base64.decode(xslt_base64);
	var xslt_dom = $.parseXML(xslt_plain);
	xslt_impl["proc"].importStylesheet(xslt_dom);

	xslt_impl["renderText"] = function(str) {
	    var xml = $.parseXML(wrapXdocFragment(str));
	    var dom = xslt_impl["proc"].transformToFragment(xml,document);
	    var str = $(dom).text();

	    // It's not clear to me whether this is good or bad.  The
	    // basic problem is that strings like "short" strings
	    // might legitimately have quotes or apostrophes in them.
	    // This is no problem if we're going to stick the
	    // renderText into a paragraph or something like that.
	    // But it *is* a problem if we're going to stick it into
	    // an attribute like a tooltip or similar.  So, just to
	    // avoid problems like that, make sure the resulting
	    // string is free of " and ' characters.
	    return String(str)
		.replace(/"/g, '&quot;')
		.replace(/'/g, '&apos;');
	};

	xslt_impl["renderHtml"] = function(str) {
	    var xml = $.parseXML(wrapXdocFragment(str));
	    var dom = xslt_impl["proc"].transformToFragment(xml,document);
	    return dom;
	};
    }
}

function renderText(str) {
    return xslt_impl["renderText"](str);
}

function renderHtml(str) {
    return xslt_impl["renderHtml"](str);
}

xsltInit();
