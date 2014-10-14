<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
<xsl:output method="html" omit-xml-declaration="yes" indent="yes"/>
<!--

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

; This is an XSLT style sheet that transforms the small XDOC markup language
; into HTML.  This is mostly straightforward.

-->

<xsl:template match="see">
  <!-- original: <a href="javascript:action_go_key('{@topic}')">
        basically worked.
        middle click didn't work. -->
  <!-- try 2: <a href="javascript:void(0)" onClick="action_go_key('{@topic}')">
        basically worked.
        middle click didn't work -->
  <!-- try 3: this broke the back button and generally seems stupid/fubar
        <a href="#" onClick="action_go_key('{@topic}')"> -->
  <!-- try 4: this seemed to totally screw up the entire page somehow
        <a href="index.html?topic={@topic}" onClick="function(e){ e.preventDefault(); action_go_key('{@topic}'); }">
       -->
  <!-- try 5: <a onClick="action_go_key('{@topic}')">
       links lose their color and mouse shape, but maybe we can fix that with css
       back button seems to work
       middle click still does nothing useful
       -->
   <!-- try 6: elaborate thing with makeSeeLinksWork() - victory but ugly
      a href="index.html?topic={@topic}" class="seelink" data-topic="{@topic}"
      -->
  <!-- try 7: reasonably sensible and works!!! woohoo!!! -->
  <a href="index.html?topic={@topic}" onclick="return dolink(event, '{@topic}');">
    <xsl:apply-templates/>
  </a>
</xsl:template>

<xsl:template match="srclink">
  <a class="srclink" title="Find-Tag in Emacs">
    <xsl:attribute name="href">javascript:srclink('<xsl:value-of select="."/>')</xsl:attribute>
    <xsl:apply-templates/>
  </a>
</xsl:template>

<xsl:template match="code">
  <pre class="code"><xsl:apply-templates/></pre>
</xsl:template>

<xsl:template match="box">
  <div class="box"><xsl:apply-templates/></div>
</xsl:template>

<xsl:template match="p">
  <p><xsl:apply-templates/></p>
</xsl:template>

<xsl:template match="blockquote">
  <blockquote><xsl:apply-templates/></blockquote>
</xsl:template>

<xsl:template match="br">
  <xsl:apply-templates/><br/>
</xsl:template>

<xsl:template match="a">
  <a href="{@href}" target="_blank">
    <nobr>
    <xsl:value-of select="."/><img src="Icon_External_Link.png" title="External link to {@href}"/>
    </nobr>
  </a>
</xsl:template>

<xsl:template match="img">
  <div class="ximg">
    <img src="./{@src}"/>
  </div>
</xsl:template>

<xsl:template match="icon">
    <img src="./{@src}"/>
</xsl:template>

<xsl:template match="b">
  <b><xsl:apply-templates/></b>
</xsl:template>

<xsl:template match="i">
  <i><xsl:apply-templates/></i>
</xsl:template>

<xsl:template match="color">
  <font color="{@rgb}"><xsl:apply-templates/></font>
</xsl:template>

<xsl:template match="sf">
  <span class="sf"><xsl:apply-templates/></span>
</xsl:template>

<xsl:template match="u">
  <u><xsl:apply-templates/></u>
</xsl:template>

<xsl:template match="v">
  <span class="v"><xsl:apply-templates/></span>
</xsl:template>

<xsl:template match="tt">
  <span class="tt"><xsl:apply-templates/></span>
</xsl:template>

<xsl:template match="ul">
  <ul><xsl:apply-templates/></ul>
</xsl:template>

<xsl:template match="ol">
  <ol><xsl:apply-templates/></ol>
</xsl:template>

<xsl:template match="li">
  <li><xsl:apply-templates/></li>
</xsl:template>

<xsl:template match="dl">
  <dl><xsl:apply-templates/></dl>
</xsl:template>

<xsl:template match="dt">
  <dt><xsl:apply-templates/></dt>
</xsl:template>

<xsl:template match="dd">
  <dd><xsl:apply-templates/></dd>
</xsl:template>

<xsl:template match="h1">
  <h1><xsl:apply-templates/></h1>
</xsl:template>

<xsl:template match="h2">
  <h2><xsl:apply-templates/></h2>
</xsl:template>

<xsl:template match="h3">
  <h3><xsl:apply-templates/></h3>
</xsl:template>

<xsl:template match="h4">
  <h4><xsl:apply-templates/></h4>
</xsl:template>

<xsl:template match="h5">
  <h5><xsl:apply-templates/></h5>
</xsl:template>

<xsl:template match="table">
  <table class="xtable"><xsl:apply-templates/></table>
</xsl:template>

<xsl:template match="tr">
  <tr><xsl:apply-templates/></tr>
</xsl:template>

<xsl:template match="th">
  <th><xsl:apply-templates/></th>
</xsl:template>

<xsl:template match="td">
  <td><xsl:apply-templates/></td>
</xsl:template>

<xsl:template match="math">
  <div class="mathblock"><xsl:value-of select="."/></div>
</xsl:template>

<xsl:template match="mathfrag">
  <span class="mathfrag"><xsl:value-of select="."/></span>
</xsl:template>



<!-- Extra stuff for Symbolic Test Vectors at Centaur -->


<xsl:template match="stv">
  <table class="stv" cellspacing="0" cellpadding="2"><xsl:apply-templates/></table>
</xsl:template>

<xsl:template match="stv_labels">
 <tr class="stv_labels"><xsl:apply-templates/></tr>
</xsl:template>

<xsl:template match="stv_inputs">
  <xsl:for-each select="stv_line">
   <tr class="stv_input_line"><xsl:apply-templates/></tr>
  </xsl:for-each>
</xsl:template>

<xsl:template match="stv_outputs">
  <xsl:for-each select="stv_line">
   <tr class="stv_output_line"><xsl:apply-templates/></tr>
  </xsl:for-each>
</xsl:template>

<xsl:template match="stv_internals">
  <xsl:for-each select="stv_line">
   <tr class="stv_internal_line"><xsl:apply-templates/></tr>
  </xsl:for-each>
</xsl:template>

<xsl:template match="stv_overrides">
  <xsl:for-each select="stv_line">
   <tr class="stv_override_line"><xsl:apply-templates/></tr>
  </xsl:for-each>
</xsl:template>

<xsl:template match="stv_name">
  <th class="stv_name"><xsl:apply-templates/></th>
</xsl:template>

<xsl:template match="stv_entry">
  <td class="stv_entry"><xsl:apply-templates/></td>
</xsl:template>

<xsl:template match="stv_label">
  <th class="stv_label"><xsl:apply-templates/></th>
</xsl:template>

</xsl:stylesheet>
