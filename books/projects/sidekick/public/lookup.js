/*

ACL2 Sidekick
Copyright (C) 2014 Kookamara LLC

Contact:

  Kookamara LLC
  11410 Windermere Meadows
  Austin, TX 78759, USA
  http://www.kookamara.com/

License: (An MIT/X11-style license)

  Permission is hereby granted, free of charge, to any person obtaining a
  copy of this software and associated documentation files (the "Software"),
  to deal in the Software without restriction, including without limitation
  the rights to use, copy, modify, merge, publish, distribute, sublicense,
  and/or sell copies of the Software, and to permit persons to whom the
  Software is furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in
  all copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
  FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
  DEALINGS IN THE SOFTWARE.

*/

var params = getPageParameters();
var what = params["lookup"];

console.log("Lookup parameter = " + what);

function count_lines (str)
{
    var n = 0;
    for(var i = 0; i < str.length; ++i)
	if (str[i] == '\n') n++;
    return n;
}

function get_disassembly (name)
{
   $.get("/disassemble", {"name":name}, function(data,textStatus,jqXHR)
   {
       var err = data[":ERROR"];
       var val = data[":VAL"];
       if (err != "NIL") {
	   $("#disassembly").html(err);
	   return;
       }
       console.log("Disassembly is " + val);
       var guts = "";
       guts += "<h4 class='secheader'><img src='icons/disassembly.png'/>Disassembly of " + htmlEncode(name) + "</h4>";
       guts += "<pre class='disassemble_out'>";
       guts += val;
       guts += "</pre>";
       $("#disassembly").html(guts);
    }).fail(function() {
	$("#disassembly").html("Error getting /disassemble result");
    });
}

function get_times ()
{
    $.get("/eventdata", {"name":what}, function(data,textStatus,jqXHR)
    {
	var err = data[":ERROR"];
	if (err != "NIL") {
	    $("#times").html("Error: " + htmlEncode(err));
	    return;
	}
	var times = "";
	var val = data[":VAL"];
	if (val == "NIL"){
	    $("#times").html("<p><small>Timings not available.</small></p>");
	    return;
	}
	var total_time = val[":TOTAL-TIME-F"];
	var prove_time = val[":PROVE-TIME-F"];
	var print_time = val[":PRINT-TIME-F"];
	var proof_tree_time = val[":PROOF-TREE-TIME-F"];
	var other_time = val[":OTHER-TIME-F"];
	var ret = "<p>";
	ret += "Took <b>" + total_time + "</b> seconds";
	if (prove_time != "0.00" ||
	    print_time != "0.00" ||
	    proof_tree_time != "0.00" ||
	    other_time != "0.00")
	{
	    ret += " &mdash; ";
	    if (prove_time != "0.00")      ret += prove_time      + " prove ";
	    if (print_time != "0.00")      ret += print_time      + " print ";
	    if (proof_tree_time != "0.00") ret += proof_tree_time + " proof-tree ";
	    if (other_time != "0.00")      ret += other_time      + " other ";
	}
	ret += "</p>";
	$("#times").html(ret);
    }).fail(function() {
	$("#times").html("Error getting times");
    });
}


var include_path_data = null;

function get_full_include_path()
{
    var guts = "";
    for(var i=0; i < include_path_data.length; ++i) {
	guts += "<li><tt>" + htmlEncode(include_path_data[i]) + "</tt></li>";
    }
    return guts;
}

function get_brief_include_path()
{
    if (include_path_data.length <= 3) {
	// Wouldn't save anything by eliding, so just show them all.
	return get_full_include_path();
    }

    var guts = "";
    guts += "<li><tt>" + htmlEncode(include_path_data[0]) + "</tt></li>";
    guts += "<li style='list-style:none' id='include_path_elided'>&nbsp; <tt>...</tt></li>";
    guts += "<li><tt>" + htmlEncode(include_path_data[include_path_data.length-1]) + "</tt></li>";
    return guts;
}

function expand_include_path() {
    $("#include_path").html(get_full_include_path());
}

function retract_include_path() {
    $("#include_path").html(get_brief_include_path());
}

function get_origin ()
{
    $.get("/origin", {"name":what}, function(data,textStatus,jqXHR)
    {
	var err = data[":ERROR"];
	if (err != "NIL") {
	    $("#origin").html("Error: " + htmlEncode(err));
	    return;
	}
	var origin = "";
	var val = data[":VAL"];
	include_path_data = val;

	if (val == "NIL"){
	    $("#origin").html("Origin not found.");
	    return;
	}
	if (val == ":BUILT-IN") {
	    origin = "<h4 class='secheader'><img src='icons/fromacl2.png'/>Built into ACL2</h4>";
	}
	else if (val == ":TOP-LEVEL") {
	    origin = "<h4 class='secheader'><img src='icons/fromsession.png'/>From current session</h4>";
	    origin += "<div id='times'></div>";
            origin += "<p>BOZO say which event number, ";
	    origin += "offer to undo through here.</p>";
	    setTimeout(get_times, 10);
	}
	else {
	    origin = "<h4 class='secheader' style='margin-bottom: 0'><img src='icons/frombook.png'/>From included book</h4>";
	    origin += "<ul id='include_path' onmouseenter='expand_include_path()' onmouseleave='retract_include_path()'>";
	    origin += get_brief_include_path();
	    origin += "</ul>";
	}
	$("#origin").html(origin);
    }).fail(function() {
	$("#origin").html("Error getting origin");
    });
}

function get_props (name)
{
    $.get("/props", {"name":name}, function(data,textStatus,jqXHR)
    {
	var err = data[":ERROR"];
	if (err != "NIL") {
	    $("#props").html(htmlEncode(err));
	    return;
	}
	var props = data[":VAL"];
	if (props == "NIL") {
	    $("#props").html("No properties found.");
	    return;
	}

	var shortrows = "";
	var longrows = "";

	for(var key in props) {
	    var keystr = key.toLowerCase().upcaseFirst().replace(/-/g, " ");
	    var val = props[key];
	    var n = count_lines(val);
	    var row = "";
	    if (n == 0) {
		row += "<tr class='short'>";
		row += " <th width='200'>" + htmlEncode(keystr) + "</th>";
  	        row += " <td><pre>" + htmlEncode(val) + "</pre></td>";
		row += "</tr>";
		shortrows += row;
	    }
	    else {
		row += "<tr class='longhead'>";
  	        row += " <th colspan='2'>" + htmlEncode(keystr) + "</th>";
		row += "</tr>";
 	        row += "<tr class='longbody'>";
		row += " <td colspan='2' style='padding-left: 1em;'>";
		row += "  <pre>" + htmlEncode(val) + "</pre>";
                row += " </td>";
                row += "</tr>";
		longrows += row;
	    }
	}

	var acc = "";
	acc += "<h4 class='secheader'><img src='icons/properties.png' />Raw Properties</h4>";
	acc += "<div id='propswrap'>";
	acc += "<table class='propstable'>";
	acc += shortrows;
	acc += longrows;
	acc += "</table>";
	acc += "</div>";

	$("#props").html(acc);

	get_disassembly(name);
    }).fail(function() {
	$("#props").html("Error getting props.");
    });
}

function get_xdoc (what)
{
    $.get("/xdoc", {"name":what}, function(data,textStatus,jqXHR)
    {
	var err = data[":ERROR"];

	var div = jQuery("<div></div>");
	var tbl  = jQuery("<table class='dochead'></table>");
	var row  = jQuery("<tr></tr>");
	var td   = jQuery("<td></td>");
	var main = jQuery("<div class='xdoc_main'></div>");

	if (err != "NIL") {
	    row.append("<td><img src='icons/documentation-none.png'/></td>");
	    td.append(htmlEncode(err));
	    row.append(td);
	    div.append(tbl);
	    main.append("<p>BOZO xdoc search when not found</p>");
	}
	else {
	    var short_xml = data[":SHORT"];
	    var long_xml = data[":LONG"];
	    row.append("<td><img src='icons/documentation.png'/></td>");
	    td.append(render_html(short_xml));
	    row.append(td);
	    main.append(render_html(long_xml));
	}

	tbl.append(row);
	div.append(tbl);
	div.append(main);

	$("#xdoc").html(div);

    }).fail(function() {
	$("#xdoc").html("Error getting /xdoc.");
    });
}

function do_lookup ()
{
    $("#what").html(htmlEncode(what));

    get_origin();
    get_props(what);
    xslt_ready(function() { get_xdoc(what); });
}

$(document).ready(do_lookup);
