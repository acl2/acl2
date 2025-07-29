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
// Compatibility wrapper for lack of XSLT standards in browsers.
//

// Warning: Keep this in sync with *entity-info*
// in ../parse-xml.lisp, and
// (defxdoc entities ...) in topics.lisp, and
// wrap_xdoc_fragment in xdata2html.pl
/**
 * Turn XDOC XML markup into a valid XML document for use with XSLT
 * below. This mainly involves adding entity references (to deal with
 * special entities that XDOC supports - see the Entities XDOC topic)
 * @param {string} str The XML markup to wrap
 * @returns {string} The wrapped XML markup, ready for use with XSLT.
 */
function wrapXdocFragment(str) {
    // We do not need any declaration for the following standard predefiend XML entities:
    // amp, lt, gt, quot, apos
    return `<!DOCTYPE xdoc [
        <!ENTITY nbsp "&#160;">
        <!ENTITY ndash "&#8211;">
        <!ENTITY mdash "&#8212;">
        <!ENTITY larr "&#8592;">
        <!ENTITY rarr "&#8594;">
        <!ENTITY harr "&#8596;">
        <!ENTITY lang "&#9001;">
        <!ENTITY rang "&#9002;">
        <!ENTITY hellip "&#8230;">
        <!ENTITY lsquo "&#8216;">
        <!ENTITY rsquo "&#8217;">
        <!ENTITY ldquo "&#8220;">
        <!ENTITY rdquo "&#8221;">
        <!ENTITY and   "&#8743;">
        <!ENTITY or    "&#8744;">
        <!ENTITY not   "&#172;">
        <!ENTITY ne    "&#8800;">
        <!ENTITY le    "&#8804;">
        <!ENTITY ge    "&#8805;">
        <!ENTITY mid   "&#8739;">
        <!ENTITY times "&#215;">
        <!ENTITY Alpha "&#913;">
        <!ENTITY Beta "&#914;">
        <!ENTITY Gamma "&#915;">
        <!ENTITY Delta "&#916;">
        <!ENTITY Epsilon "&#917;">
        <!ENTITY Zeta "&#918;">
        <!ENTITY Eta "&#919;">
        <!ENTITY Theta "&#920;">
        <!ENTITY Iota "&#921;">
        <!ENTITY Kappa "&#922;">
        <!ENTITY Lambda "&#923;">
        <!ENTITY Mu "&#924;">
        <!ENTITY Nu "&#925;">
        <!ENTITY Xi "&#926;">
        <!ENTITY Omicron "&#927;">
        <!ENTITY Pi "&#928;">
        <!ENTITY Rho "&#929;">
        <!ENTITY Sigma "&#931;">
        <!ENTITY Tau "&#932;">
        <!ENTITY Upsilon "&#933;">
        <!ENTITY Phi "&#934;">
        <!ENTITY Chi "&#935;">
        <!ENTITY Psi "&#936;">
        <!ENTITY Omega "&#937;">
        <!ENTITY alpha "&#945;">
        <!ENTITY beta "&#946;">
        <!ENTITY gamma "&#947;">
        <!ENTITY delta "&#948;">
        <!ENTITY epsilon "&#949;">
        <!ENTITY zeta "&#950;">
        <!ENTITY eta "&#951;">
        <!ENTITY theta "&#952;">
        <!ENTITY iota "&#953;">
        <!ENTITY kappa "&#954;">
        <!ENTITY lambda "&#955;">
        <!ENTITY mu "&#956;">
        <!ENTITY nu "&#957;">
        <!ENTITY xi "&#958;">
        <!ENTITY omicron "&#959;">
        <!ENTITY pi "&#960;">
        <!ENTITY rho "&#961;">
        <!ENTITY sigma "&#963;">
        <!ENTITY tau "&#964;">
        <!ENTITY upsilon "&#965;">
        <!ENTITY phi "&#966;">
        <!ENTITY chi "&#967;">
        <!ENTITY psi "&#968;">
        <!ENTITY omega "&#969;">
        <!ENTITY forall "&#8704;">
        <!ENTITY exist "&#8707;">
        <!ENTITY empty "&#8709;">
        <!ENTITY isin "&#8712;">
        <!ENTITY notin "&#8713;">
        <!ENTITY prod "&#8719;">
        <!ENTITY sum "&#8721;">
        <!ENTITY ccedil "&#231;">
        <!ENTITY aacute "&#225;">
        <!ENTITY agrave "&#224;">
        <!ENTITY acirc "&#226;">
        <!ENTITY atilde "&#227;">
        <!ENTITY auml "&#228;">
        <!ENTITY aring "&#229;">
        <!ENTITY egrave "&#232;">
        <!ENTITY eacute "&#233;">
        <!ENTITY ecirc "&#234;">
        <!ENTITY euml "&#235;">
        <!ENTITY igrave "&#236;">
        <!ENTITY iacute "&#237;">
        <!ENTITY icirc "&#238;">
        <!ENTITY iuml "&#239;">
        <!ENTITY ntilde "&#241;">
        <!ENTITY ograve "&#242;">
        <!ENTITY oacute "&#243;">
        <!ENTITY ocirc "&#244;">
        <!ENTITY otilde "&#245;">
        <!ENTITY ouml "&#246;">
        <!ENTITY ugrave "&#249;">
        <!ENTITY uacute "&#250;">
        <!ENTITY ucirc "&#251;">
        <!ENTITY uuml "&#252;">
        <!ENTITY Ccedil "&#199;">
        <!ENTITY Aacute "&#193;">
        <!ENTITY Agrave "&#192;">
        <!ENTITY Acirc "&#194;">
        <!ENTITY Atilde "&#195;">
        <!ENTITY Auml "&#196;">
        <!ENTITY Aring "&#197;">
        <!ENTITY Egrave "&#200;">
        <!ENTITY Eacute "&#201;">
        <!ENTITY Ecirc "&#202;">
        <!ENTITY Euml "&#203;">
        <!ENTITY Igrave "&#204;">
        <!ENTITY Iacute "&#205;">
        <!ENTITY Icirc "&#206;">
        <!ENTITY Iuml "&#207;">
        <!ENTITY Ntilde "&#209;">
        <!ENTITY Ograve "&#210;">
        <!ENTITY Oacute "&#211;">
        <!ENTITY Ocirc "&#212;">
        <!ENTITY Otilde "&#213;">
        <!ENTITY Ouml "&#214;">
        <!ENTITY Ugrave "&#217;">
        <!ENTITY Uacute "&#218;">
        <!ENTITY Ucirc "&#219;">
        <!ENTITY Uuml "&#220;">

    ]>
    <root>${str}</root>`;
}

/**
 * Fix quotes in a DOM node. Modifies the DOM node in-place.
 * @param {Node} node The DOM node to fix quotes in.
 */
function unfuglifyLegacyQuotes (node) {
    switch(node.nodeType) {
        case Node.ELEMENT_NODE:
            // Don't fix up quotes when there is code involved.
            // Unfortunately we have to keep this in sync with render.js
            const tag = node.tagName.toLowerCase();
            if (tag == "pre" || tag == "tt" || tag == "code")
                return;

            const cl = node.getAttribute("class");
            if (cl == "v" || cl == "tt" || cl == "mathfrag" || cl == "mathblock")
                return;
        break;

        case Node.TEXT_NODE:
            let text = node.nodeValue;
            // Apparently we can't use html entities here like &ldquo; or you end
            // up with something like &amp;ldquo; in your document.  Fortunately the
            // unicode escapes work.  Thanks stackoverflow.
            text = text.replace(/``/g, '\u201c')   // ldquo, smart `` quote
                    .replace(/''/g, '\u201d')   // rdquo, smart '' quote
                    .replace(/`/g,  '\u2018')   // lsquo, smart ` quote
                    .replace(/'/g,  '\u2019');  // rsquo, smart ' quote
            node.nodeValue = text;
        break;
    }

    for(let i = 0; i < node.childNodes.length; ++i) {
        const child = node.childNodes[i];
        unfuglifyLegacyQuotes(child);
    }
}

class XdocRenderer {
    constructor() {
        this.ready = false;
    }

    /**
     * Set up a XSLT processor with the given template source.
     * @param {string} xsltSource The source of the XSLT template.
     */
    init(xsltSource) {
        this.proc = new XSLTProcessor();
        const xslt_dom = new DOMParser().parseFromString(xsltSource, "text/xml");
        this.proc.importStylesheet(xslt_dom);
        this.ready = true;
    }

    /**
     * Render some content written in the XDoc markup language to plain text.
     * @param {string} str The content to render.
     * @returns {string} The content, rendered as plain text.
     */
    renderText(str) {
        if(!this.ready) {
            console.error("Unable to render text before XSL template is loaded.");
        }
        const xml = new DOMParser().parseFromString(wrapXdocFragment(str), "text/xml");
        const dom = this.proc.transformToFragment(xml,document);
        const outStr = dom.textContent;

        // It's not clear to me whether this is good or bad.  The
        // basic problem is that strings like "short" strings
        // might legitimately have quotes or apostrophes in them.
        // This is no problem if we're going to stick the
        // renderText into a paragraph or something like that.
        // But it *is* a problem if we're going to stick it into
        // an attribute like a tooltip or similar.  So, just to
        // avoid problems like that, make sure the resulting
        // string is free of " and ' characters.
        return String(outStr)
            .replace(/"/g, '&quot;')
            .replace(/'/g, '&apos;');
    }

    /**
     * Render some content written in the XDoc markup language to DOM elements.
     * @param {string} str The content to render.
     * @returns {DocumentFragment} The content, rendered to a HTML DOM tree.
     */
    renderHtml(str) {
        if(!this.ready) {
            console.error("Unable to render text before XSL template is loaded.");
        }
        const xml = new DOMParser().parseFromString(wrapXdocFragment(str), "text/xml");
        const dom = this.proc.transformToFragment(xml,document);
        unfuglifyLegacyQuotes(dom);
        return dom;
    }
}
