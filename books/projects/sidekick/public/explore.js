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
	div.append("<p class='sf'>Top-level hypotheses</p>");
	var tbl = "<table class='hyps'>";
	for(var i = 0; i < hyps.length; ++i) {
	    var hyp = hyps[i];
	    var row = "<tr>";
	    row += "<th>" + i + ".</th>";
  	    row += "<td><pre>" + htmlEncode(hyp) + "</pre></td>";
	    row += "</tr>";
	    tbl += row;
	}
	tbl += "</table>";
	div.append(tbl);
    }

    var curr = "<p class='sf'>Current term</p>";
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
	setTimeout(get_goal_loop, 200);
    }).fail(function() {
	$("#goal").html("<p>Error getting <tt>th</tt> information.</p>");
	setTimeout(get_goal_loop, 200);
    });
}

$(document).ready(function(){
   get_goal_loop();
});
