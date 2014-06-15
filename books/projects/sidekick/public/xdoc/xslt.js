/*
; XDOC Documentation System for ACL2
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>
*/

// xslt.js
//
// Compatbility wrapper for lack of XSLT standards in browsers.
//
// Interface:
//   render_text(String of XDOC XML markup) -> String of Plain Text
//   render_html(String of XDOC XML markup) -> HTML DOM Object

function wrap_xdoc_fragment(str) {
    var wrap = "<!DOCTYPE xdoc [";
    wrap += "<!ENTITY mdash \"&#8212;\">";
    wrap += "<!ENTITY rarr \"&#8594;\">";
    wrap += "<!ENTITY nbsp \"&#160;\">";
    wrap += "]>";
    wrap += "<root>" + str + "</root>";
    return wrap;
}

var xslt_impl = {};
var xslt_ready = false;

function xslt_init() {

    // BOZO need to reinstall IE support

    // Initialize an XSLT processor for XDOC --> HTML conversion
    var xhttp = new XMLHttpRequest();
    xhttp.open("GET", "/xdoc/render.xsl", true);
    xhttp.onreadystatechange = function()
    {
        if (xhttp.readyState == 4 && xhttp.status == 200) {
	    var xslt = xhttp.responseXML;
	    xslt_impl["proc"] = new XSLTProcessor();
	    xslt_impl["proc"].importStylesheet(xslt);

	    xslt_impl["render_text"] = function(str) {
		var xml = $.parseXML(wrap_xdoc_fragment(str));
		var dom = xslt_impl["proc"].transformToFragment(xml,document);
		var str = $(dom).text();

		// It's not clear to me whether this is good or bad.  The
		// basic problem is that strings like "short" strings
		// might legitimately have quotes or apostrophes in them.
		// This is no problem if we're going to stick the
		// render_text into a paragraph or something like that.
		// But it *is* a problem if we're going to stick it into
		// an attribute like a tooltip or similar.  So, just
		// to avoid problems like that, make sure the
		// resulting string is free of " and ' characters.
		return String(str)
		    .replace(/"/g, '&quot;')
		    .replace(/'/g, '&apos;');
	    };

	    xslt_impl["render_html"] = function(str) {
		var xml = $.parseXML(wrap_xdoc_fragment(str));
		var dom = xslt_impl["proc"].transformToFragment(xml,document);
		return dom;
	    }

	    xslt_ready = true;
	}
    }
    xhttp.send();
}

function render_text(str) {
    if (xlst_ready)
	return xslt_impl["render_text"](str);
    else
	return "XSLT not ready.";
}

function render_html(str) {
    if (xslt_ready)
	return xslt_impl["render_html"](str);
    else
	return "XSLT not ready.";
}

xslt_init();
