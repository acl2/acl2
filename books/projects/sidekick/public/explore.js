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

var DELAY = 250;

function contrapose_with(n)
{
    $.ajax({url: "/explore-contrapose",
            type: "POST",
	    data: {"n":n},
	    cache: false,
	    success: function(data,textStatus,jqXHR) {
		var err = data[":ERROR"];
		if (err != "NIL") {
		    window.alert("Contrapose with " + n + " failed: " + err);
		}
		// Else, everything is fine, display will update soon, nothing to do
	    },
	    fail: function() {
		window.alert("Contrapose with " + n + " failed!");
	    }
    });
    return false;
}

function demote(n)
{
    $.ajax({url: "/explore-demote",
            type: "POST",
	    data: {"n":n},
	    cache: false,
	    success: function(data,textStatus,jqXHR)
	    {
		var err = data[":ERROR"];
		if (err != "NIL") {
		    window.alert("Demote " + n + " failed: |" + err + "|");
		}
		// Else, everything is fine, display will update soon, nothing to do
	    },
	    fail: function() {
		window.alert("Demote " + n + " failed!");
	    }
    });
    return false;
}

function drop(n)
{
    $.ajax({url: "/explore-drop",
            type: "POST",
	    data: {"n":n},
	    cache: false,
	    success: function(data,textStatus,jqXHR)
	    {
		var err = data[":ERROR"];
		if (err != "NIL") {
		    window.alert("Drop " + n + " failed: |" + err + "|");
		}
		// Else, everything is fine, display will update soon, nothing to do
	    },
	    fail: function() {
		window.alert("Drop " + n + " failed!");
	    }
    });
    return false;
}

function split()
{
    $.ajax({url: "/explore-split",
            type: "POST",
	    cache: false,
	    success: function(data,textStatus,jqXHR)
	    {
		var err = data[":ERROR"];
		if (err != "NIL") {
		    window.alert("Split failed: |" + err + "|");
		}
		// Else, everything is fine, display will update soon, nothing to do
	    },
	    fail: function() {
		window.alert("Split failed!");
	    }
    });
    return false;
}

function pro()
{
    $.ajax({url: "/explore-pro",
            type: "POST",
	    cache: false,
	    success: function(data,textStatus,jqXHR)
	    {
		var err = data[":ERROR"];
		if (err != "NIL") {
		    window.alert("Pro failed: |" + err + "|");
		}
		// Else, everything is fine, display will update soon, nothing to do
	    },
	    fail: function() {
		window.alert("Pro failed!");
	    }
    });
    return false;
}

// BOZO port to uncacheable ajax
function undo_to(n)
{
    $.post("/explore-undo", {"n":n},function(data,textStatus,jqXHR)
    {
	var err = data[":ERROR"];
	if (err != "NIL") {
	    window.alert("Undo through " + n + " failed: " + err);
	}
	// Else, everything is fine, display will update soon, nothing to do
    }).fail(function() {
	window.alert("Undo through " + n + " failed!");
    });
    return false;
}

function format_goal(goal)
{
    var hyps = goal[":HYPS"];
    var conclusion = goal[":CONCLUSION"];
    var current_addr = goal[":CURRENT-ADDR"];
    var current_term = goal[":CURRENT-TERM"];
    if (hyps == "NIL") hyps = [];

    var div = jQuery("<div></div>");

    if (hyps.length != 0)
    {
	var head = "";
	head += "<p class='sf'>";
	head += "<a href='#' ";
	head += "   title='Demote all hypotheses, pushing them into the conclusion.'";
	head += "   onclick='demote(\"\")');'>";
	head += "<img src='icons/explore-demote.png'/>";
	head += "</a>";
	head += " Top-level hypotheses &nbsp; ";
	head += "</p>";

	var tbl = "<table class='hyps'>";
	for(var i = 0; i < hyps.length; ++i) {
	    var hyp = hyps[i];
	    var row = "<tr>";
//	    row += "<th>" + (i+1) + ".</th>";

	    row += "<td style='padding-right: .5em;'>";
	    row += "<a href='javascript:void(0)' title='Contrapose this hypothesis and the conclusion.' onclick='contrapose_with(" + (i+1) + ");'>";
	    row += "<img src='icons/explore-contrapose.png'/>";
	    row += "</a>";
	    row += "</td>";

	    row += "<td style='padding-right: .5em;'>";
	    row += "<a href='javascript:void(0)' title='Demote this hypothesis, pushing it into the conclusion.' onclick='demote(" + (i+1) + ");'>";
	    row += "<img src='icons/explore-demote.png'/>";
	    row += "</a>";
	    row += "</td>";

	    row += "<td style='padding-right: .5em;'>";
	    row += "<a href='javascript:void(0)' title='Drop this hypothesis.' onclick='drop(" + (i+1) + ");'>";
	    row += "<img src='icons/explore-drop.png'/>";
	    row += "</a>";
	    row += "</td>";

  	    row += "<td><pre>" + htmlEncode(hyp) + "</pre></td>";

	    row += "</tr>";
	    tbl += row;
	}
	tbl += "</table>";

	div.append(head);
	div.append(tbl);
    }

    var curr = "<p class='sf'>";
    curr += "<a href='javascript:void(0)' ";
    curr += "   title='Promote terms from IMPLIES structure into hypotheses'";
    curr += "   onclick='pro()');'>";
    curr += "<img src='icons/explore-split.png'/>";
    curr += "</a>";
    curr += " Current term &nbsp; ";
    curr += "</p>";

    curr += "<div class='current_term'>";
    curr += "<pre>";
    curr += htmlEncode(current_term);
    curr += "</pre>";
    div.append(curr);
    return div;
}

function get_goal_loop()
{
    $.get("/explore-th", null, function(data,textStatus,jqXHR)
    {
	var err = data[":ERROR"];
	var val = data[":VAL"];
	var msg = "";

	if (err == "Not currently verifying a formula.")
	{
	    msg += "<p><b>Error:</b> " + htmlEncode(err) + "</p>";
	    msg += "<p>Use <tt>(verify &lt;formula&gt;)</tt> to start.</p>";
	}

	else if (err != "NIL")
	{
	    msg += "<p><b>Error:</b> " + htmlEncode(err) + "</p>";
	}

	else
	{
	    msg = format_goal(val);
	}

	$("#goal").html(msg);
	setTimeout(get_goal_loop, DELAY);
    }).fail(function() {
	$("#goal").html("<p>Error getting <tt>th</tt> information.</p>");
	setTimeout(get_goal_loop, DELAY);
    });
}

function format_commands(cmds)
{
    var div = jQuery("<div></div>");
    if (cmds.length != 0)
    {
	div.append("<p class='sf'>Commands</p>");
	var tbl = "<table class='commandlist'>";
	for(var i = 0; i < cmds.length; ++i)
	{
	    var cmd = cmds[i];
	    var idx = cmd[":INDEX"];
	    var form = cmd[":COMMAND"];

	    if (idx == "NIL") {
		continue;
	    }

	    tbl += "<tr>";
	    tbl += "<td>";
	    tbl += "<a href='#' title='Undo through this command' onclick='undo_to(" + idx + ");'>";
  	    tbl += "<img src='icons/session-undo.png'/>";
	    tbl += "</a>";
	    tbl += "</td>";
	    // Showing the numbers seems useful for command-line proof-builder users because they can
	    // say where to undo through, but it seems less useful for the web interface and I don't
	    // at all like the jarring way that the numbers are ordered.  If we simply reversed the
	    // indices and had the new commands have the highest numbers, there would be far greater
	    // continuity after undoing.  For now I'm just going to hide the command numbers. 
	    // tbl += "<th>" + idx + "</th>";
	    tbl += "<td><pre>" + form + "</pre></td>";
	    tbl += "</tr>";
	}
	tbl += "<tr><td colspan='2'><i><small>Oldest</small></i></tr>";
	tbl += "</table>";
	div.append(tbl);
    }
    else
    {
	div.append("<p class='sf'>No Commands Yet</p>");
    }
    return div;
}

function get_commands_loop()
{
    $.get("/explore-commands", null, function(data,textStatus,jqXHR)
    {
	var err = data[":ERROR"];
	var val = data[":VAL"];
	var msg = "";

	if (err != "NIL") {
	    msg += "<p><b>Error:</b> " + htmlEncode(err) + "</p>";
	}
	else {
	    msg = format_commands(val);
	}

	$("#commands").html(msg);
	setTimeout(get_commands_loop, DELAY);
    }).fail(function() {
	$("#commands").html("<p>Error getting commands.</p>");
	setTimeout(get_commands_loop, DELAY);
    });
}

$(document).ready(function(){
   get_goal_loop();
   get_commands_loop();
});
