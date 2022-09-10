(in-package "ACL2S")

(include-book "xdoc/top" :dir :system)

(defxdoc acl2s-installation
  :parents (acl2::acl2-sedan)
  :short "Describes how to install ACL2s"
  :long
"
<h3>Installing ACL2s</h3>

<p>
For specific instructions on how to install ACL2s on your computer,
please select the appropriate topic below:
</p>

<ul>
<li>@(see acl2s-installation-windows)</li>
<li>@(see acl2s-installation-macos)</li>
<li>@(see acl2s-installation-linux)</li>
</ul>
")

(defxdoc acl2s-installation-windows
  :parents (acl2s-installation)
  :short "Installation instructions for ACL2s on Windows"
  :long
"
<h3>Description</h3>
<p>
To run ACL2s on Windows, we will use
<a href=\"https://docs.microsoft.com/en-us/windows/wsl/about\">WSL 
(the Windows Subsystem for Linux)</a>. This allows us to run the
Linux version of Eclipse and ACL2s on Windows machines.
</p>

<p>
Note that there is a FAQ at the bottom of this topic. Check there
first if you run into any issues!
</p>

<h3>Requirements</h3>
<ul>
  <li>at least 8GB of free hard drive space</li>
  <li>at least 4GB of RAM</li>
  <li>Windows 10 version 21H1 or greater. Windows 11 may also work.</li>
</ul>

<p>
Installation should take less than an hour, though installation time
will depend on your computer's specs and on the speed of your internet
connection. You can use your computer while the installation is
occurring.
</p>

<h3>Instructions</h3>
<ol>
<li>Install WSL
  <ol>
  <li>Open an administrator terminal (either CMD or Powershell). This
  can be done by opening the Windows menu at the bottom left hand
  side of the screen and searching for @('cmd'). Then, right click
  on the \"Command Prompt\" item and select \"Run as administrator\".</li>
  <li>Run @('wsl --install')</li>
  <li>NOTE: if the above command does not work, try installing Ubuntu
  from the Windows App Store.</li>
  <li>If this command finishes saying \"A reboot is required\", you
  should reboot your computer.</li>
  </ol>
</li>
<li>Set up a user account in WSL
  <ol>
  <li>After rebooting (if neccesary), a window titled \"Ubuntu\" should
  pop up saying \"Installing, this may take a few minutes...\"</li>
  <li>If no such window pops up, open the Windows menu, search for
  \"Ubuntu\", and run it.</li>
  <li>Follow the prompts for creating a new user account in WSL. You
  can choose whatever username and password you like, they do not
  need to be the same as your Windows username and password.</li>
  </ol>
</li>
<li>Install Xming and launch it
  <ol>
  <li>Download the installer
  <a href=\"https://cs2800.atwalter.com/cs2800/Xming-6-9-0-31-setup.exe\"><b>here</b></a>
  and run it.</li>
  <li><strong>Do not</strong> uncheck the option to associate .xlaunch files with
  Xming during installation! <strong>Do</strong> uncheck the option to launch
  Xming after the installation is complete.</li>
  <li>Download our Xming launch profile
  <a href=\"https://cs2800.atwalter.com/cs2800/ACL2sXming.xlaunch\"><b>here</b></a>
  and put it somewhere memorable. <b>You may need to right-click on
  the link and select \"Save As...\" if your browser doesn't
  download it automatically.</b></li>
  <li>Double click on our Xming launch profile to start Xming. If
  Windows asks you which networks you want to allow Xming to
  access, make sure you allow it to access both private and
  public networks.</li>
  </ol>
</li>
<li>Download and run our installation script
<ol>
  <li>Ensure that the following command is run as a <b>non-root
  user</b>. If the Ubuntu terminal starts with @('root@...') when you start
  it up, you are running as a root user. Otherwise, you are OK.</li>
  <li>In the Ubuntu shell, run @({wget \"cs2800.atwalter.com/cs2800/wsl.sh\" && chmod +x wsl.sh})
  to download and set the script as runnable.</li>
  <li>Then, run @({./wsl.sh}). The script will prompt for your password
  one or more times. When it prompts during the Homebrew install,
  just press enter to accept the default installation directory.</li>
  <li>Run <code>source ~/.profile</code></li>
</ol>
</li>
<li>Create a folder for your CS2800 files on your @('C:') drive
<ol>
  <li>Open File Explorer, select \"This PC\" on the left, double click
  on \"Local Disk (C:)\", right-click on an empty area inside of
  that folder, and select \"New Folder\". Name the folder whatever
  you would like.</li>
</ol>
</li>
<li>Run Eclipse
<ol>
  <li>Run @({./eclipse/eclipse})</li>
  <li>When Eclipse asks for a workspace, enter @('/mnt/c/<FOLDER>'),
  where @('<FOLDER>') should be replaced with the name of the folder
  that you just created.</li>
</ol>
</li>
<li>Get started with Eclipse
<ol>
  <li>Create a new Eclipse project by selecting New -&gt; Project... -&gt;
  General -&gt; Project and giving it a name (whatever you would
  like)</li>
  <li>Right click on the project on the left hand side of the screen
  and select New -&gt; Other... -&gt; ACL2s -&gt; ACL2s/Lisp file. Change
  the name of the file if you'd like, and leave the rest of the
  settings untouched. Click \"Finish\".</li>
  <li>Click on the green \"play\" button at the top of the
  screen: <icon src=\"res/acl2s/icons/acl2_restart.gif\" alt=\"restart session\"/>
  Eclipse will ask you if you want it to certify system
  books; click \"Yes\".</li>
  <li>After Eclipse pops up a window saying that certification is
  done, click on the green \"play\" button again.</li>
  <li>Type @('(+ 1 1)') in the @('.lisp') file that you created, and click
  on the icon with the single down arrow at the top of the
  screen. Confirm that @('2') is eventually shown in the @('.lisp.a2s')
  file that Eclipse generated. If so, your installation is
  working!</li>
</ol>
</li>
</ol>
")

(defxdoc acl2s-installation-macos
  :parents (acl2s-installation)
  :short "Installation instructions for ACL2s on macOS"
  :long
  "
<h3 id=\"requirements\">Requirements</h3>
<ul>
<li>at least 5GB of free hard drive space</li>
<li>at least 4GB of RAM</li>
<li>macOS Catalina (10.15), Big Sur (11), or Monterey (12)</li>
</ul>
<p>Installation should take less than an hour, though installation time
will depend on your computer's specs and on the speed of your internet
connection. You can use your computer while the installation is
occurring.</p>

<h3 id=\"instructions\">Instructions</h3>
<p>A video walking through installation is available
<a href=\"https://youtu.be/AFluHK99-A0\" target=\"_blank\">here</a>.</p>
<ol>
<li>Determine if your Mac uses an M1 processor and check your macOS version<ol>
<li>Click on the Apple icon at the top left of the screen and
select \"About This Mac\". On the screen that pops up, check the
text next to \"Processor\" or \"Chip\". If the text includes
\"Apple\", you have an M1 processor in your Mac. Otherwise, if
the text includes \"Intel\", you have an x86 Mac.</li>
<li>In the \"About This Mac\" window, double check that you are
running one of \"macOS Catalina\", \"macOS Big Sur\", or \"macOS
Monterey\". If you are using a different version of macOS, you
will likely need to use the Khoury Virtual Desktops
Infrastructure (VDI).</li></ol></li>
<li>Install Homebrew<ol>
<li>Open the Terminal app, either by searching for it or via
opening Finder and selecting Go -&gt; Utilities in the menu bar,
and opening Terminal in that folder.</li>
<li>Go to <a href=\"https://brew.sh\">brew.sh</a> and copy-paste the
command starting with <code>/bin/bash</code> on the top of that page
into a Terminal window, then press enter. You only need to run that
single command, and can safely ignore the other instructions on
Homebrew's website. You may need to enter your password one or more
times throughout the process.</li>
</ol></li>
<li>Tap and install ACL2s<ol>
<li>Run <code>brew tap mister-walter/acl2s</code> and then <code>brew install acl2s --force-bottle</code> inside of Terminal.</li></ol></li>
<li>Install Java<ol>
<li>Download and install Java 17. The easiest way to do this is to go to <a href=\"https://www.oracle.com/java/technologies/downloads/#jdk17-mac\">this link</a>
and download either the Arm64 DMG installer (if you are on a M1
Mac) or the x64 DMG installer. Then, open the DMG and run the
installer inside of it.</li></ol></li>
<li>Install Eclipse<ol>
<li>Download the Eclipse version appropriate for your machine: <a href=\"https://cs2800.atwalter.com/cs2800/eclipse-platform-4.21-macosx-cocoa-aarch64.dmg\">M1
Mac</a>
or <a href=\"https://cs2800.atwalter.com/cs2800/eclipse-platform-4.21-macosx-cocoa-x86_64.dmg\">x86
Mac</a>.</li>
<li>Open the downloaded file and click and drag the Eclipse icon
  into your Applications folder.</li>
<li><b>If you already have Eclipse installed</b>, you should still
install the version of Eclipse we provide here. If you need your
existing Eclipse install for another class, you can install Eclipse
for this class by dragging the Eclipse icon into a different folder
(for example, a folder on your Desktop) rather than Applications.</li>
</ol></li>
<li>Install the ACL2s Eclipse Plugin<ol>
<li>Open Eclipse, either by searching for it or via opening Finder
and selecting Go &rarr; Applications in the menu bar, and opening
Eclipse in that folder.</li>
<li>Select the folder that you want to keep all of your CS2800 ACL2
files in. You can use the default choice if you like. You may
also want to check the box that says \"Use this as the default
and do not ask again\". Then, click \"Launch\".</li>
<li>In the menu bar, click on Help &rarr; Install New Software...</li>
<li>Click on \"Add...\" in the screen that comes up. In the resulting
window, enter @('ACL2s') next to \"Name:\" and
@('http://cs2800.atwalter.com/p2') next to \"Location\". Then, click
\"Add\", which will close the pop-up.</li>
<li>The middle of the window should now show \"ACL2s Plugin Update
Site\". Click on the checkbox to the left of it and click \"Next&gt;\" 
at the bottom of the window.</li>
<li>In the next window, click \"Finish\" at the bottom right of the
screen. If a pop-up appears that says \"Warning: Installing
unsigned software for which the authenticity or validity cannot
be established. Continue with installation?\", click \"Install
anyway\".</li>
<li>After the installation is complete, Eclipse will ask you if you
would like to restart Eclipse Platform. Select \"Restart
Now\". This will close Eclipse and reopen it.</li></ol></li>
<li>Get started with Eclipse<ol>
<li>Create a new Eclipse project by selecting New &rarr; Project... &rarr;
General &rarr; Project and giving it a name (whatever you would
like)</li>
<li>Right click on the project on the left hand side of the screen
and select New &rarr; Other... &rarr; ACL2s &rarr; ACL2s/Lisp file. Change
the name of the file if you'd like, and leave the rest of the
settings untouched. Click \"Finish\".</li>
<li>Click on the green \"play\" button at the top of the
screen: <icon src=\"res/acl2s/icons/acl2_restart.gif\" alt=\"restart session\"/>
Eclipse will ask you if you want it to certify system
books; click \"Yes\".</li>
<li>After Eclipse pops up a window saying that certification is
done, click on the green \"play\" button again.</li>
<li>Type <code>(+ 1 1)</code> in the @('.lisp') file that you created, and click
on the icon with the single down arrow at the top of the
screen. Confirm that <code>2</code> is eventually shown in the @('.lisp.a2s')
file that Eclipse generated. If so, your installation is
working!</li></ol></li>
</ol>
")

(defxdoc acl2s-installation-linux
  :parents (acl2s-installation)
  :short "Installation instructions for ACL2s on Linux"
  :long
  "
<h3 id=\"requirements\">Requirements</h3>
<ul>
<li>At least 5GB of free hard drive space</li>
<li>At least 4GB of RAM</li>
<li>An Intel or AMD processor</li>
</ul>
<h3 id=\"instructions\">Instructions</h3>
<p>These instructions are known to work on Ubuntu 20.04, and may work on
other platforms as well. If you run into any issues, feel free to
reach out to Drew.</p>
<ol>
<li>Ensure the following software is installed on your machine. If not,
install using your Linux distribution's package manager.<ul>
<li>Java 11 or greater (OpenJDK is fine too) (<code>openjdk-11-jre</code> or newer on Ubuntu)</li>
<li><code>git</code></li>
<li><code>curl</code></li>
<li><code>procps</code></li>
<li><code>file</code></li>
<li>\"Development tools\" (<code>build-essential</code> on Ubuntu)</li></ul><ol>
<li>If you are on an older version of Ubuntu, you may need to install <code>libswt-gtk-4-jni</code> and <code>xutils-dev</code> as well.</li></ol></li>
<li>Install Homebrew<ol>
<li>Go to <a href=\"https://brew.sh\">brew.sh</a> and copy-paste the
command starting with <code>/bin/bash</code> on the top of that page
into a terminal shell, then press enter. You only need to run that
single command, and can safely ignore the other instructions on
Homebrew's website. You may need to enter your password one or more
times throughout the process.</li>
</ol></li>
<li>Tap and install ACL2s<ol>
<li>Run <code>brew tap mister-walter/acl2s</code> and then <code>brew install acl2s --force-bottle</code> inside of a terminal. <b>Do not</b> follow any of Homebrew's suggestions regarding installing <code>gcc</code>.</li></ol></li>
<li>Install Eclipse<ol>
<li>Download <a href=\"https://cs2800.atwalter.com/cs2800/eclipse-with-plugins.tar.gz\">our Eclipse archive</a> and unpack it somewhere on your computer.</li>
<li>Run Eclipse by running <code>./eclipse/eclipse</code> from the directory
that you unpacked the Eclipse package inside of.</li></ol></li>
<li>Get started with Eclipse<ol>
<li>Create a new Eclipse project by selecting New &rarr; Project... &rarr;
General &rarr; Project and giving it a name (whatever you would
like)</li>
<li>Right click on the project on the left hand side of the screen
and select New &rarr; Other... &rarr; ACL2s &rarr; ACL2s/Lisp file. Change
the name of the file if you'd like, and leave the rest of the
settings untouched. Click \"Finish\".</li>
<li>Click on the green \"play\" button at the top of the
screen: <icon src=\"res/acl2s/icons/acl2_restart.gif\" alt=\"restart session\"/>
Eclipse will ask you if you want it to certify system
books; click \"Yes\".</li>
<li>After Eclipse pops up a window saying that certification is
done, click on the green \"play\" button again.</li>
<li>Type <code>(+ 1 1)</code> in the @('.lisp') file that you created, and click
on the icon with the single down arrow at the top of the
screen. Confirm that <code>2</code> is eventually shown in the @('.lisp.a2s')
file that Eclipse generated. If so, your installation is
working!</li></ol></li>
</ol>
")


