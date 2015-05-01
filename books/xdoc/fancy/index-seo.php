<?php
   // ><html><body><h1> Sorry, no php enabled, this won't work! </h1></body></html><!--
   // settings:
   
   $top = 'ACL2____TOP'; // top topic
   $notFound = 'DOCNOTFOUND'; // not found topic
   $index = 'DOCINDEX'; // index page
   
   $basedir=pathinfo($_SERVER["SCRIPT_NAME"],PATHINFO_DIRNAME)."/";
   $scriptdir=$_SERVER["SCRIPT_NAME"].'/';
   error_reporting(E_ALL);
   ini_set('display_errors', 1);
   
   // function to prevent SQL injection attacks. Unfortunately, there
   // seems to be no alternative for SQLite, and no documentation on
   // what the function does exactly, so we err on the safe side:
   if(!function_exists('sqlite_escape_string')){ 
       function sqlite_escape_string($string) {
       // only allow characters which we know occur in the keys
           if (preg_match('/^[-._A-Za-z0-9]+$/',$string)===false)
           // returns 0 on a match, which evaluates to false, so we need a
           // check with three ='s
             return '';
           else return $string; // the string is safe!
       }
   }

   class MyDB extends SQLite3
   {
      function __construct()
      {
         $this->open('xdata-seo.db');
      }
   }
   $db = new MyDB();
   if(!$db){
      echo $db->lastErrorMsg();
      exit();
   }
   
   if(isset($_SERVER["PATH_INFO"]) && (strlen($_SERVER["PATH_INFO"])>1))
        $key = pathinfo($_SERVER["PATH_INFO"],PATHINFO_BASENAME);
   else $key = $top;
   $showIndex=false;
   if($key=="*") {$showIndex=true;$key=$index;unset($_GET['path']);}
   
   $ret = $db->query("SELECT * from xdoc_data where XKEY='".sqlite_escape_string($key)."'");
   $page = $ret->fetchArray(SQLITE3_ASSOC);
   
   if(!$page || $page['XKEY']!=$key){
     header("HTTP/1.0 404 Not Found");
     $key  = $notFound;
     $ret  = $db->query("SELECT * from xdoc_data where XKEY='".$key."'");
     $page = $ret->fetchArray(SQLITE3_ASSOC);
   }else 
   if(!$showIndex){
     $preferedURL=$scriptdir.$page['XKEY'];
     header("Content-Location: ".$preferedURL);
   }
   
   if(!$page) { // fallback when not even the 404 page was found
     header("Location: ".$scriptdir);
     die();
   }
   
   
   $lookup = array($page['ID']=>$page);
   $lookupx = array($page['XKEY']=>$page);
   if(isset($_GET['path'])) $path_idea = explode('/',$_GET['path']); else $path_idea = array();
   $path_reversed=array();
   $cur = $page;
   $parents = explode(',',substr($cur['PARENTIDS'],1,-1));
   while (count($parents)) {
     $candidates = array_intersect($path_idea,$parents);
     if(count($candidates)){ // found something (hopefully one)
       $path_idea = array_diff($path_idea,$parents);
       $nextID = array_pop($candidates);
     }else{
       $nextID = $parents[0]; // nothing found, pick first parent
     }
     if(isset($lookup[$nextID])){ // loop found! Abort
       $parents = array();
     }else{
       $ret = $db->query("SELECT * from xdoc_data where ID='".sqlite_escape_string($nextID)."'");
       $cur = $ret->fetchArray(SQLITE3_ASSOC);
       if($cur){
         $lookup[$cur['ID']] = $cur;
         $path_reversed[] = $cur['ID'];
         $parents = explode(',',substr($cur['PARENTIDS'],1,-1));
       }else $parents = array();
     }
   }; // while (count($parents));
   $path=$page['ID'];
   foreach($path_reversed as $itm){
     $path=$itm.'/'.$path;
   }
   
   function lookup_by_id($id){
     global $lookup, $lookupx, $db;
     if(!isset($lookup[$id])){
       $ret = $db->query("SELECT * from xdoc_data where ID='".sqlite_escape_string($id)."'");
       $cur = $ret->fetchArray(SQLITE3_ASSOC);
       $lookup[$cur['ID']] = $cur;
       $lookupx[$cur['XKEY']] = $cur;
     }
     return $lookup[$id];
   }
   function lookup_by_xkey($xkey){
     global $lookup, $lookupx, $db;
     if(!isset($lookupx[$xkey])){
       $ret = $db->query("SELECT * from xdoc_data where XKEY='".sqlite_escape_string($xkey)."'");
       $cur = $ret->fetchArray(SQLITE3_ASSOC);
       $lookup[$cur['ID']] = $cur;
       $lookupx[$cur['XKEY']] = $cur;
     }
     return $lookupx[$xkey];
   }
   
   function disp($str){
     global $scriptdir;
     echo str_replace(
        array('<see topic="'        ,'</see>','<code>'            ,'</code>')
       ,array('<a href="'.$scriptdir,'</a>'  ,'<pre class="code">','</pre>')
       ,$str);
   }
?><!DOCTYPE html>
<html>
<head>
<?php
  if(isset($preferedURL)){ echo '<link rel="canonical" href="http://'.$_SERVER['SERVER_NAME'].$preferedURL.'" />'; }
?>
<meta charset="UTF-8">
<!--
; Original author: Jared Davis <jared@centtech.com>
; PHP version by Sebastiaan Joosten
; Content by various authors
-->
<title><?php echo($page['PACKAGE'] .' - '. $page['TITLE']); ?></title>
<link rel="stylesheet" type="text/css" href="<?= $basedir ?>desktop.css"/>
<link rel="shortcut icon" href="<?= $basedir ?>favicon.png"/>
</head>
<body>

<div id="top">

  <table border="0" id="toolbar">
    <tr>
      <th>
	<a href="<?= $scriptdir ?>ACL2____TOP">
	  <img class="toolbutton" src="<?= $basedir ?>xdoc-home.png"
	       data-powertip="<p>Go to the Top topic.</p>">
	</a>&nbsp; &nbsp;</th><th>
	<a href="<?= $scriptdir ?>*">
	  <img class="toolbutton" src="<?= $basedir ?>view_flat.png"
	       data-powertip="<p>View sitemap.</p>"/>
	</a>
	<a target="DownloadWindow" href="<?= $basedir ?>download/manual.zip">
	  <img class="rtoolbutton" src="<?= $basedir ?>download.png"
	       data-powertip="<p>Download a zipped copy of this manual (for
	       faster or offline browsing).</p>"/>
	  </a>
      </th>
      <td><label style="color:white">
	  Search-engine friendly clone of the <a href="http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/" style="color:white;text-decoration:underline">ACL2 documentation</a>.
	  </label>
      </td>
    </tr>
  </table>

</div>

<div id="left">
  <div id="nav"><UL>
    <?php
      $cur = lookup_by_xkey($top);
      $path_reversed[] = $page['ID'];
      function show_rec($cur,$newpath){
        global $path_reversed, $scriptdir;
        echo '<LI style="list-style-type:';
        if(strlen($cur['CHILDREN'])) echo 'disc'; else echo 'circle';
        echo '"><nobr><A HREF="'.$scriptdir.$cur['XKEY'].'?path='.$newpath.'" title="'.htmlentities(strip_tags($cur['SHORTDESC'])).'">'.$cur['TITLE'].'</A></nobr>';
        if(array_search($cur['ID'],$path_reversed)!==FALSE){
          $children=explode(',',$cur['CHILDREN']);
          if(count($children)){
            echo '<UL>';
            for($i=1;$i<count($children);$i++){
              $kid=lookup_by_xkey($children[$i]);
              show_rec($kid,$newpath.'/'.$kid['ID']);
            }
            echo '</UL>';
          }
        }
      }
      show_rec($cur,$cur['ID']);
    ?></UL>
  </div>
</div>

<div id="right">
  <?php
  $ps=explode(',',substr($page['PARENTIDS'],1,-1));
  function ispos($x){return strlen($x)&&(-$x<1);}
  $ps = array_filter($ps,"ispos");
  if(count($ps)){ ?>
    <div id="parents">
    <UL> <?php
      foreach($ps as $id){
        $cur=lookup_by_id($id);
        echo '<li><a id="'.$id.'" href="'.$scriptdir.$cur['XKEY'].'?path='.$path.'"';
        echo ' title="'.htmlentities(strip_tags($cur['SHORTDESC'])).'">'.$cur['TITLE'].'</a></li>';
      } ?>
    </UL></div><?php
  }
  
  ?>
  <div id="data">
    <H1><?php echo $page['TITLE']; ?></H1>
    <P align="center"><?php
     disp($page['SHORTDESC']);
    ?></P>
    <?php
     disp($page['LONGDESC']);
     if($showIndex){
        echo '<UL>';
        $ret = $db->query("SELECT XKEY,TITLE,SHORTDESC,PACKAGE from xdoc_data ORDER BY TITLE");
        while($cur=$ret->fetchArray(SQLITE3_ASSOC)){
          if(strlen($cur['PACKAGE'])){
            echo '<LI><a href="'.$scriptdir.$cur['XKEY'].'" title="'.htmlentities(strip_tags($cur['SHORTDESC'])).'">';
            echo $cur['TITLE'];
            echo '</a></li>';
          }
        }
        echo '</UL>';
     }else
     if(strlen($page['CHILDREN'])){
       ?><H3>Subtopics</H3>
       <DL>
       <?php
        $childs = explode(',',$page['CHILDREN']);
        for($i=1;$i<count($childs);$i++){
          $cur = lookup_by_xkey($childs[$i]);
          echo '<DT><a href="'.$scriptdir.$cur['XKEY'].'?path='.$path.'">';
          echo $cur['TITLE'];
          echo '</a></dt><dd>';
          disp($cur['SHORTDESC']);
          echo'</dd>';
        }
     }
     
    $db->close();
    ?>
  </div>
</div>
</body>
</html>