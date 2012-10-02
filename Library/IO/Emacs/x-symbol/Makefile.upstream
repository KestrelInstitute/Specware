### Makefile --- create binary package of X-Symbol

## Copyright (C) 1998-2003 Free Software Foundation, Inc.
##
## Author: Christoph Wedler <wedler@users.sourceforge.net>
## Version: 4.5.X
## Keywords: fonts, WYSIWYG, LaTeX, HTML, wp, math
## X-URL: http://x-symbol.sourceforge.net/

# This software is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by the
# Free Software Foundation; either version 2, or (at your option) any
# later version.

# This software is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
# for more details.

# You should have received a copy of the GNU General Public License
# along with This software; see the file COPYING.  If not, write to
# the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
# Boston, MA 02111-1307, USA.

### Commentary:

## This Makefile is for X-Symbol developers (esp. the author) using XEmacs,
## only!  Use Makefile.emacs for Emacs.  This file `include's a modified
## version of the generic XEmacs Package Makefile "XEmacs.rules".  For details,
## see <info:(xemacs)Building Packages>.

## The following targets might be interesting:
##  - clean: delete the generated files
##  - binball: build /tmp/staging/x-symbol-X.YY-pkg.tar.gz
##  - srckit: build /tmp/staging/x-symbol-X.YY-src.tar.gz
##  - info: create the info file (to check)
##  - elc: create the elc files (to check)
##  - www: create tar.gz for web pages incl manual (personal use only)
##  - release: create all tar.gz files for new version (personal use only)

### Code:

## VERSION is a float!
VERSION = 4.51
AUTHOR_VERSION = 4.5.1
MAINTAINER = Christoph Wedler <wedler@users.sourceforge.net>
PACKAGE = x-symbol
PKG_TYPE = regular
REQUIRES = xemacs-base
CATEGORY = wp
RELEASEDIR = $(HOME)/public_html/x-symbol
PACKAGEDIR = $(HOME)/.xemacs/xemacs-packages

## nil if you want to use XEmacs-21' feature of uninterned symbols in
## macros
XMAS20 = nil

## other program settings after "include ./XEmacs.rules" below
ZIP = gzip -v9
MAKEINFO_FLAGS = -I ./man --no-split

###===========================================================================
## Shouldn't be interesting from now on... (except "include ./XEmacs.rules")

ELCS = lisp/x-symbol-hooks.elc lisp/x-symbol-macs.elc \
	lisp/x-symbol-vars.elc lisp/x-symbol.elc \
	lisp/x-symbol-image.elc lisp/x-symbol-sgml.elc \
	lisp/x-symbol-tex.elc lisp/x-symbol-bib.elc \
	lisp/x-symbol-texi.elc
## now Emacs version dependend files (no autoloads, no custom)
MULE_ELCS = lisp/x-symbol-mule.elc lisp/x-symbol-nomule.elc \
	lisp/x-symbol-xmacs.elc

DATA_DEST = $(PACKAGE)
DATA_FILES = Makefile.emacs \
	etc/colormap138.xpm etc/RIP.xbm etc/drawing.xbm etc/escherknot.xbm \
	etc/hourglass.xbm etc/recycle.xbm etc/termlock.xbm

DATA_1_DEST = $(PACKAGE)/fonts
DATA_1_FILES = fonts/Makefile fonts/makesub \
	fonts/nilxs.bdf \
	fonts/2helvR12.bdf fonts/3helvR12.bdf fonts/5etl14.bdf \
	fonts/heriR12.bdf fonts/xsymb0_12.bdf fonts/xsymb1_12.bdf \
	fonts/2helvR14.bdf fonts/3helvR14.bdf fonts/5etl16.bdf \
	fonts/heriR14.bdf fonts/xsymb0_14.bdf fonts/xsymb1_14.bdf

DATA_2_DEST = $(PACKAGE)/origfonts
DATA_2_FILES = origfonts/helvR12.bdf origfonts/helvR14.bdf

DATA_3_DEST = $(PACKAGE)/pcf
DATA_3_FILES = pcf/fonts.dir pcf/*.pcf

DATA_4_DEST = $(PACKAGE)/genfonts
DATA_4_FILES = genfonts/*.bdf

INFO_FILES = man/x-symbol.info*
TEXI_FILES = man/Makefile man/x-symbol.texi man/x-symbol.css man/x-symbol.init

WWW_FILES = www/changes.txt www/style.css www/overview.tex.txt \
	www/index.html www/related.html www/details.html www/news.html \
	www/addfonts.html \
	www/colors.png www/context.png www/grid.png \
	www/images.png www/key.png www/overview.png www/subscripts.png \
	www/token.png

MANUAL = x-symbol

AUTOLOAD_PATH = lisp

###===========================================================================
include ./XEmacs.rules
## preserve, the .el files could be newer than the .elc files otherwise)
RCOPY = cp -p
## follow symbolic links
TAR = tar -h
###===========================================================================

GENERATED += lisp/custom-load.elc

EXCLUDES += --exclude 'RCS' --exclude '*.elc' --exclude '*.aux' \
	--exclude '*.cp' --exclude '*.dvi' \
	--exclude 'genfonts' --exclude 'pcf' \
	--exclude 'Also' --exclude 'Fonts' --exclude 'Old' --exclude 'Tests' \
	--exclude 'Utils' --exclude 'doc' --exclude 'release' \
	--exclude 'www' --exclude 'admin' --exclude 'dated'

EXTRA_SOURCES = lisp/x-symbol-emacs.el

ifeq ($(XMAS20),t)
PRELOADS = -eval "(setq byte-compile-print-gensym nil)"
else
PRELOADS =
endif
PRELOADS += -eval "(progn (if (featurep 'x-symbol-autoloads) (unload-feature 'x-symbol-autoloads)) (push \"`pwd`/lisp/\" load-path))" -l auto-autoloads.el

ifeq ($(PEDANTIC),t)
PRELOADS += -eval "(setq stack-trace-on-error t)"
## every file with name matching "x-symbol" will be load/required uncompiled
PRELOADS += -eval "(progn \
  (defadvice require (before require activate) \
    (or filename \
	(not (string-match \"x-symbol\" (symbol-name feature))) \
	(setq filename (format \"%s.el\" feature)))) \
  (defadvice load (before load activate) \
    (or nosuffix \
	(string-match \"\\\\.el\\\\'\" file) \
	(not (string-match \"x-symbol\" (file-name-nondirectory file))) \
	(setq file (format \"%s.el\" file) nosuffix t))))"
endif

# With XEmacs-21.1, -vanilla now only includes -no-early-packages, not
# -no-packages.  This is not useful at all.  If there is a decent function to
# get the load-path of packages in $(REQUIRES), I would use it.  If
# package-compile.el could be used without changing my file structure, I would
# probably use it.

all:: lisp/auto-autoloads.el $(MULE_ELCS) $(ELCS) \
	lisp/auto-autoloads.elc lisp/custom-load.elc info fonts

elcs: lisp/auto-autoloads.el $(MULE_ELCS) $(ELCS) \
	lisp/auto-autoloads.elc lisp/custom-load.elc

info: man/x-symbol.texi
	$(MAKE) -C man x-symbol.info

fonts:
	$(MAKE) -C fonts mkdirs
	$(MAKE) -C fonts pcfs

.PHONY: srckit test release fonts info elcs

srckit: srckit-std

clean: mostlyclean
	$(MAKE) -C man clean
	$(MAKE) -C fonts clean

binkit: binkit-common

www: $(STAGING)/x-symbol/www.tar.gz

release: srckit man/index.html man/x-symbol.ps binball www
	$(MAKE) -C release VERSION=$(VERSION) release

wwwrelease: www
	$(MAKE) -C release VERSION=$(VERSION) release

man/index.html: man/x-symbol.texi man/x-symbol.init
	$(MAKE) -C man html

man/x-symbol.ps: man/x-symbol.texi
	$(MAKE) -C man ps

man/x-symbol.pdf: man/x-symbol.texi
	$(MAKE) -C man pdf

$(STAGING)/x-symbol/www.tar.gz: $(WWW_FILES) man/index.html man/x-symbol.css \
				 man/x-symbol.ps man/x-symbol.pdf
	if [ ! -d $(STAGING)/x-symbol/man ]; \
		then mkdir -p $(STAGING)/x-symbol/man; fi
	rm -f $(STAGING)/x-symbol/man/*
	$(RCOPY) $(WWW_FILES) $(STAGING)/x-symbol
	$(RCOPY) man/x-symbol.css man/index.html man/x-symbol*.html \
		man/x-symbol.ps man/x-symbol.pdf $(STAGING)/x-symbol/man
##	$(ZIP) -f $(STAGING)/x-symbol/man/x-symbol.ps
##	$(ZIP) -f $(STAGING)/x-symbol/man/x-symbol.pdf
	$(CHMOD) $(STAGING)/x-symbol/*
	$(CHMOD) $(STAGING)/x-symbol/man/*
	(cd $(STAGING)/x-symbol; \
		$(TAR) -cf www.tar $(notdir $(WWW_FILES)) man; \
		$(ZIP) -f www.tar)
