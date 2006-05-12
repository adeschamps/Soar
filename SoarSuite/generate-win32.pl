#!/usr/bin/perl
#
# New installer generation script.
#
# Assumptions:
# Run in Cygwin, svn in path

# Overview:
#Creation of the windows installer is done using the perl script in the root of the SoarSuite tree, <code>generate-win32.pl</code>.  This script assumes a lot of conditions and will fail violently if said conditions are not met.

# The installer creation script proceeds through a number of steps:
# Call rebuild-all.bat rebuilding everything in the current tree in release mode. If you know everything is built and up-to-date, you can skip this step by passing <code>-nobuild</code> on the command line.
# Check out source from svn.  This goes up a dir, creates a dir using the name and version specified in the script (see below) and appends <code>-source</code> to the directory name.  This directory represends the "Source" module of the install.
# Remove stuff from the just checked out tree that should not be included in the install.  This uses an array of globs in the perl script to delete files from the source tree that should not be included in the release.
# Removes the old <code>-core</code> dir if it exists (see step 5)
# Creates <code>-core</code> dir next to the <code>-source</code> dir (up one level) by copying out specific binaries from the working copy.  These are binaries it just built in step 1.
# Moves stuff from <code>-source</code> to <code>-core</code>, stuff that needs to be installed to run Soar.  This works in the same way as the copies from the working copy, by using an array in the script.
# Generates NSI script.  This step takes an input file (in the root of SoarSuite, .nsi.in) and parses it creating the installer output file, substituting the files from the <code>-core</code> and <code>-source</code> directories and other things as necessary.
# Converts forward slashes to backslashes in the script file.  Forward slashes are easier to work with in the file, so this is done in its own step.
# Compiles installer using makensis.

use strict;
use File::Find::Rule;
use File::Copy::Recursive qw/rcopy rmove/;
use File::Copy;
use File::Path;

##################
# Variables

# SVN url
my $soarurl = "https://winter.eecs.umich.edu/svn/soar/trunk/SoarSuite";

# Name and version
my $nameandversion = "Soar Suite 8.6.2-r8";

# File globs to completely remove from the tree (not distributed at all)
my @remove = qw/INSTALL .cvsignore .svn *.xcodeproj *.so *.so.2 *.jnilib java_swt make-mac-app.sh *.plist *.doc *.ppt *.pl *.am *.ac *.m4 Figures ManualSource Old *.tex/;

# Globs to copy from working copy to Core component
# WORKING --copy-to-> CORE
my @copyglobs = qw(*.pdf *.dll *.exe *.jar *.tcl ClientSML.lib ElementXML.lib ConnectionSML.lib Tcl_sml_ClientInterface mac towers-of-hanoi-SML.soar);

# Globs to MOVE from Source component to Core component
# SOURCE --move-to-> CORE
my @moveglobs = qw/COPYING Documentation Resources SoarLibrary agents maps templates *.bat/;

# Nullsoft installer script input file
my $nsiinput = "8.6.2.nsi.in";

# Nullsoft installer script output file
my $nsioutput = "Soar-Suite-8.6.2.nsi";

# Location of NSIS executable (makensis.exe)
my $makensis = "/cygdrive/c/Program\\ Files\\ \\(x86\\)/NSIS/makensis.exe";
##################

my $namedashes = $nameandversion;
$namedashes =~ tr/ /-/;
my $core = "../$namedashes-core";
my $source = "../$namedashes-source";
my $msprogramsname = $nameandversion;
$msprogramsname =~ s/Suite //;

# Parse command line options
my $build = 1;
my $checkout = 1;
my $nsionly = 0;
my @dirstodelete;
my @filestodelete;

foreach (@ARGV) {
	if ($_ eq "-nobuild") {
		$build = 0;
	} elsif ($_ eq "-nocheckout") {
		$checkout = 0;
	} elsif ($_ eq "-nsionly") {
		$nsionly = 1;
	}
}

if ($nsionly) {
	&nsi_step;
	exit(0);
}

if ($build == 1) {
	&build_step;
}

if ($checkout == 1) {
	&checkout_step;
}

&copy_step;
&move_step;
&nsi_step;
exit(0);

################################
# subroutines

sub build_step {
	print "Step 1: Rebuild everything...\n";
	system "rebuild-all.bat";
}

sub checkout_step { 
	print "Step 2: Check out source from SVN...\n";
	rmtree($source);
	system "svn export $soarurl $source --native-eol CRLF";
	
	print "Step 3: Remove globs from source that are not to be distributed with the release...\n";

	foreach (File::Find::Rule->file()->name(@remove)->in($source)) {
		print "Removing from source: $_\n";
		unlink $_ or die "Unable to remove $_: $!";
	}

	foreach (File::Find::Rule->directory()->name(@remove)->in($source)) {
		print "Removing from source: $_\n";
		rmtree($_) or die "Unable to remove $_: $!";
	}
}

sub copy_step {
	print "Step 4: Remove old core tree...\n";
	rmtree($core, 1);
	print "Step 5: Copy globs from working tree to core...\n";
	foreach (File::Find::Rule->directory()->name(@copyglobs)->in("."), File::Find::Rule->file()->name(@copyglobs)->mindepth(2)->in(".")) {
		# This creates destination if it doesn't exist.
		print "Copying to core: $_\n";
		rcopy($_, "$core/$_");
	}
}

sub move_step {
	print "Step 6: Move globs from source tree to core...\n";
	foreach(File::Find::Rule->directory()->name(@moveglobs)->in($source), File::Find::Rule->file()->name(@moveglobs)->in($source)) {
		# This creates destination if it doesn't exist.
		print "Moving from source to core: $_\n";
		/$source(.*)/;
		my $outputdir = $1;
		rcopy($_, "$core/$outputdir");
	}
	
	print "Step 6.1: Rename COPYING...\n";
	rmove("$core/COPYING", "$core/License.txt");
	
	print "Step 6.2: Remove svn dirs from core...\n";
	foreach (File::Find::Rule->directory()->name(".svn")->in($core)) {
		print "Removing from core: $_\n";
		rmtree($_) or die "Unable to remove $_: $!";
	}
	
	print "Step 6.3: Remove svn dirs from source...\n";
	foreach (File::Find::Rule->directory()->name(".svn")->in($source)) {
		print "Removing from source: $_\n";
		rmtree($_) or die "Unable to remove $_: $!";
	}
}

sub nsi_step {
	print "Step 7: Generate NSI installer script...\n";
	open(NSIINPUT, $nsiinput) or die "Couldn't open nsi input file: $!";
	open(NSIOUTPUT, ">$nsioutput") or die "Couldn't open nsi output file: $!";

	while(<NSIINPUT>) {
		if (/(.*)nameandversion(.*)/) {
			print NSIOUTPUT $1 . $nameandversion . $2 . "\n";
		} elsif (/(.*)installdir(.*)/) {
			print NSIOUTPUT $1 . "Soar/" . $namedashes . $2 . "\n";
		} elsif (/(.*)outfile(.*)/) {
			print NSIOUTPUT $1 . $namedashes . ".exe" . $2 . "\n";
		} elsif (/(.*)msprogramsname(.*)/) {
			print NSIOUTPUT $1 . $msprogramsname . $2 . "\n";
		} elsif (/(.*)corefiles(.*)/) {
			&do_files ($core);
		} elsif (/(.*)sourcefiles(.*)/) {
			&do_files ($source);
		} elsif (/\s*CreateShortCut\s*\"(.+?)\"/) {
			push(@filestodelete, $1);
			print NSIOUTPUT $_;		
		} elsif (/\s*CreateDirectory\s*\"(.+?)\"/) {
			push(@dirstodelete, $1);
			print NSIOUTPUT $_;		
		} elsif (/(.*)deletefiles(.*)/) {
			# Delete "Filename"
			foreach (@filestodelete) {
				print NSIOUTPUT "\tDelete \"$_\"\n";
			}
		} elsif (/(.*)deletedirs(.*)/) {
			# RMDir "Dirname"
			for (my $i = @dirstodelete - 1; $i >= 0; --$i) {
				print NSIOUTPUT "\tRMDir \"@dirstodelete[$i]\"\n";
			}
		} else {
			print NSIOUTPUT $_;		
		}
	}
	close (NSIINPUT);
	close (NSIOUTPUT);

	print "Step 8: Convert forward slashes to backslashes...\n";
	open (NSIINPUT, $nsioutput);
	my @nsiinput = <NSIINPUT>;
	close (NSIINPUT);
	open (NSIOUTPUT, ">$nsioutput");
	foreach (@nsiinput) {
		my $output = $_;
		if ($_ !~ /http:\/\//) {
			if ($_ =~ /([^"]*)"(.*)"(.*)/) {
				my $slashes = $2;
				$slashes =~ tr/\//\\/;
				$output = "$1\"$slashes\"$3\n";
			}
		}
		print NSIOUTPUT $output;
	}
	close (NSIOUTPUT);

	print "Step 9: Create installer...\n";
	system "$makensis $nsioutput";
}

sub do_files {
	foreach (File::Find::Rule->directory->in($_[0])) {
		my $currentdir = $_;
		/$_[0](.*)/;
		my $outputdir = $1;
		print NSIOUTPUT "\n\tSetOutPath \"\$INSTDIR$outputdir\"\n";
		push (@dirstodelete, "\$INSTDIR$outputdir");
				
		foreach (File::Find::Rule->file->maxdepth(1)->in("$currentdir")) {
			print NSIOUTPUT "\tFile \"$_\"" . "\n";
			/.*\/(.*)$/;
			push (@filestodelete, "\$INSTDIR$outputdir" . '/' . $1);
		}
	}
}
