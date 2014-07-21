<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">

<!--

; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
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

  xml-topic.xsl  -  directly stylize .xml files for use in a web browser

  This is basically html-core.xsl, with .xml file extensions on <see> links.

-->

<xsl:include href="html-core.xsl"/>

<xsl:template match="parent">
  <p>Parent: <a href="{@topic}.xml">
    <xsl:value-of select="."/>
  </a></p>
</xsl:template>

<xsl:template match="see">
  <a href="{@topic}.xml">
    <xsl:apply-templates/>
  </a>
</xsl:template>

<xsl:template match="hindex">
  <li><nobr><xsl:choose>
	<xsl:when test="@kind='leaf'">
           <img src="leaf.png"/>
        </xsl:when>

        <xsl:when test="@kind='show'">
           <a href="JavaScript:toggleVisible('{@id}')">
             <img id="img-{@id}" src="minus.png" border="0"/>
           </a>
        </xsl:when>

        <xsl:when test="@kind='hide'">
           <a href="JavaScript:toggleVisible('{@id}')">
             <img id="img-{@id}" src="plus.png" border="0"/>
           </a>
	</xsl:when>
      </xsl:choose>
      <a href="{@topic}.xml" title="{hindex_short}">
	<xsl:value-of select="hindex_name"/>
     </a></nobr>
    <xsl:apply-templates/>
  </li>
</xsl:template>

</xsl:stylesheet>
