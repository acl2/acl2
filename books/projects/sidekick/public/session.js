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

var pbt_ldds  = null;    // Cache of LDDs from :PBT until a new history is entered
var pc_cache  = [];      // Cache of :pc results for hovering
var pcb_cache = [];      // Cache of :pcb results
var pcb_full_cache = []; // Cache of :pcb! results

function clear_caches()
{
    pc_cache = [];
    pcb_cache = [];
    pcb_full_cache = [];
}

function enter_pbt_entry(n)
{
    console.log("Enter " + n);
    // Mouse enters PBT display line: expand entry using :PC command
    var look = pc_cache[n];
    if (look) {
	$("#pbt_form_" + n).html(look);
	return;
    }
    $.get("/pc", {"num":n},
    function(data,textStatus,jqXHR) {
	var ldd = data[":VAL"];
	var form = ldd[":FORM"];
	var ans = htmlEncode(form);
	pc_cache[n] = ans;
	$("#pbt_form_" + n).html(ans);
    }).fail(
    function() {
	$("#pbt_form_" + n).html("Error getting entry " + n);
    });
}

function exit_pbt_entry(n)
{
    console.log("Exit " + n);
    // Mouse exits PBT display line: collapse entry back to what PBT prints
    var ldd = pbt_ldds[n];
    var form = ldd[":FORM"];
    $("#pbt_form_" + n).html(htmlEncode(form));
}

function show_pcb(n, full)
{
    var cache = full ? pcb_full_cache : pcb_cache;
    var look = cache[n];
    if (look) {
	console.log("pcb cache hit.");
	$("#pcb").html(look);
	return;
    }
    $("#pcb").html("Loading...");
    $.get("/pcb", {"num":n,"full":full}, function(data,textStatus,jqXHR) {
	var ldds = data[":VAL"];
	var div = jQuery("<table class='pcb_table'></table>");
	for(var i in ldds) {
	    var ldd = ldds[i];
	    var cls = ldd[":CLASS"];
	    var form = ldd[":FORM"];
	    var mode = ldd_mode(ldd);
	    var disabled = ldd_disabled(ldd);
	    var row = "<tr>";
	    row += "<td class='" + mode + " " + disabled + "'>";
	    row += "<pre class='pcb_form'>" + htmlEncode(form) + "</pre>";
//	    row += "<br/>CLASS: " + cls; 
	    row += "</td>";
	    row += "</tr>";
	    div.append(row);
	}
	cache[n] = div;
	$("#pcb").html(div);
    }).fail(function() {
	$("#pcb").html("Error getting pcb");
    });
}

function ldd_mode(ldd)
{
    var orig = ldd[":ORIG-SYMBOL-CLASS"];
    var curr = ldd[":CURRENT-SYMBOL-CLASS"];
    return (curr == "V") ? "pbt_verified"
	 : (curr == "L") ? "pbt_logic"
         : (orig == "V") ? "pbt_verified"
	 : (orig == "L") ? "pbt_logic"
         : (orig == "P") ? "pbt_program"
	 : "";
}

function ldd_disabled(ldd)
{
    // if (ldd[":MOST-RECENT"] == "T")
    //    return "pbt_recent";
    if (ldd[":DISABLED"] == "D")
	return "pbt_disabled";
    else if (ldd[":DISABLED"] == "d")
	return "pbt_part_disabled";
    else
	return "pbt_enabled";
}

function undo_back_through(n)
{
    $.post("/ubt", {"n":n},function(data,textStatus,jqXHR)
    {
	var err = data[":ERROR"];
	if (err != "NIL") {
	    window.alert("Undo back through " + n + " failed: " + err);
	}
	// Else, everything is fine, display will update soon, nothing to do
    }).fail(function() {
	window.alert("Undo back through " + n + " failed!");
    });
    return false;
}

var pbt_last_row = null;
function render_pbt(ldds)
{
    var tbl = jQuery("<table class='pbt_table'></table>");
    pbt_ldds = ldds;
    for(var i in ldds) {
	var ldd = ldds[i];
	var n = ldd[":N"];
	var form = ldd[":FORM"];
	var mode = ldd_mode(ldd);
	var disabled = ldd_disabled(ldd);

	var row = "";
	row += "<tr class='pbt_line " + disabled + "'>";
	row += "<th>" + n + "</th>";
	row += "<td class='pbt_form " + mode + "'";
        row += " onMouseEnter='enter_pbt_entry(" + n + ")'";
        row += " onMouseLeave='exit_pbt_entry(" + n + ")'";
        row += " onClick='show_pcb(" + n + ", 1)'>";
	row += "<pre id='pbt_form_" + n + "'>" + htmlEncode(form) + "</pre>";
	row += "</td>";

	row += "<td>";
	row += "<a href='#' title='Undo back through here' onclick='undo_back_through(" + n + ");'>";
	row += "<img src='icons/session-undo.png' title='Undo back through here.'/>";
	row += "</a>";
	row += "</td>";

	row += "</tr>\n";
	tbl.append(row);
	pbt_last_row = n;
    }
    return tbl;
}

function refresh_pbt_loop()
{
    $.get("/pbt", null, function(data,textStatus,jqXHR)
    {
	var is_new = data[":NEW"];
	var never_showed_anything = !pbt_ldds;
	if (is_new || never_showed_anything)
	{
	    // Need to display the updated data.
	    clear_caches();
	    var tbl = render_pbt(data[":VAL"]);
	    $("#pbt").html(tbl);
	    setTimeout(scroll_to_bottom, 10);

	    // Special case: If this is the first time we've gotten new data,
	    // then we are on our initial load of the page and we should not
	    // do anything more here because the :pcb window is displaying the
	    // welcome/help message.
	    //
	    // However, subsequently, as the user submits commands to ACL2, it
	    // is nice to automatically load the most recently submitted command
	    // into the :pcb window.
	    if (!never_showed_anything) {
		console.log("Auto pcb'ing " + pbt_last_row);
		show_pcb(pbt_last_row, 1);
	    }
	}
	setTimeout(refresh_pbt_loop, 200);
    }).fail(function() {
	$("#pbt").html("Error getting pbt.");
	setTimeout(refresh_pbt_loop, 200);
    });
}

function scroll_to_bottom ()
{
    console.log("Scrolling to bottom");
    var page_height = $("#pbt").height();
    var win_height  = $("#pbtwrap").height();
    var target = page_height - win_height;
    if (target < 0) target = 0;
    // console.log("page_height = " + page_height);
    // console.log("win_height = " + win_height);
    // console.log("target = " + target);
    $("#pbtwrap").scrollTop(target);
}

$(document).ready(function(){
   refresh_pbt_loop();
});
