all: pdf htm zip

SLM= SpecwareLanguageManual
SLMDIR= $(SLM).htm-dir
SLMTAR= $(SLMDIR).tar
SLMTARBOL= $(SLMTAR).gz

pdf: $(SLM).pdf

htm: $(SLMDIR)

htmbol: htm
	tar cf - $(SLMDIR) | gzip > $(SLMTARBOL)

zip: pdf htm
	rm -f $(SLM).zip
	zip -r $(SLM).zip $(SLMDIR) Makefile $(SLM).dbk bookinfo.glm disclaimer.glm intro.glm metaslang.glm grammar.glm libraries.glm

ARCH= i586
#ARCH= sparc
BIN= ../bin/$(ARCH)
GLM2DBKMS= $(BIN)/glm2dbk -metaslang
GLM2DBKGR= $(BIN)/glm2dbk -grammar

#DB2PDF= ../bin/db2pdf
DB2PDF= ../bin/db2pdf -E9999

#DB2HTML= ../bin/db2html
DB2HTML= ../bin/db2html -E9999

ADJUSTFONTHTML= bin/adjustFontHTML
ANCHORHTML= bin/anchorHTML
REANCHORGRAMMARHTML= bin/reAnchorGrammarHTML
NAVLINKHTML= bin/navLinkHTML

PDFDBK= bookinfo.dbk \
        disclaimer.dbk \
        intro.dbk \
        metaslang.dbk \
        grammar.dbk \
        libraries.dbk

$(SLM).pdf: Makefile $(SLM).dbk $(PDFDBK)
	@if test -r $(SLM).pdf; \
	 then /bin/mv -f $(SLM).pdf $(SLM).pdf.old; \
	 fi
	($(DB2PDF) $(SLM).dbk 2>&1) | grep -v 'is not a function name'

HTMDBK= bookinfo-htm.dbk \
        disclaimer-htm.dbk \
        intro-htm.dbk \
        metaslang-htm.dbk \
        grammar-htm.dbk \
        libraries-htm.dbk

$(SLMDIR): Makefile $(SLM)-htm.dbk $(HTMDBK) \
    $(ADJUSTFONTHTML) $(ANCHORHTML) $(NAVLINKHTML) $(REANCHORGRAMMARHTML)
	($(DB2HTML) $(SLM)-htm.dbk 2>&1) | grep -v 'is not a function name'
	/usr/bin/find db2html-dir -name '*.html' \
		-exec $(ADJUSTFONTHTML) {} \;
	/usr/bin/find db2html-dir -name '*.html' \
		-exec $(ANCHORHTML) {} \;
	/usr/bin/find db2html-dir -name '*.html' \
		-exec $(NAVLINKHTML) {} \;
	$(REANCHORGRAMMARHTML) db2html-dir/grammar.html
	/bin/mv db2html-dir/book1.html db2html-dir/$(SLM).html
	@/bin/rm -rf $(SLMDIR).old
	@if test -r $(SLMDIR); \
	 then /bin/mv -f $(SLMDIR) $(SLMDIR).old; \
	 fi
	/bin/mv db2html-dir $(SLMDIR)

$(SLM).dbk:

$(SLM)-htm.dbk: Makefile $(SLM).dbk
	@if test -r $(SLM)-htm.dbk; \
	 then /bin/mv -f $(SLM)-htm.dbk $(SLM)-htm.dbk.old; \
	 fi
	sed 's/.dbk/-htm.dbk/g' $(SLM).dbk > $(SLM)-htm.dbk


bookinfo.dbk: Makefile bookinfo.glm
	@if test -r bookinfo.dbk; \
	 then /bin/mv -f bookinfo.dbk bookinfo.dbk.old; \
	 fi
	$(GLM2DBKMS) -pdf bookinfo.glm > bookinfo.dbk

disclaimer.dbk: Makefile disclaimer.glm
	@if test -r disclaimer.dbk; \
	 then /bin/mv -f disclaimer.dbk disclaimer.dbk.old; \
	 fi
	$(GLM2DBKMS) -pdf disclaimer.glm > disclaimer.dbk

intro.dbk: Makefile intro.glm
	@if test -r intro.dbk; \
	 then /bin/mv -f intro.dbk intro.dbk.old; \
	 fi
	$(GLM2DBKMS) -pdf intro.glm > intro.dbk

metaslang.dbk: Makefile metaslang.glm
	@if test -r metaslang.dbk; \
	 then /bin/mv -f metaslang.dbk metaslang.dbk.old; \
	 fi
	$(GLM2DBKMS) -pdf metaslang.glm > metaslang.dbk

usage.dbk: Makefile usage.glm
	@if test -r usage.dbk; \
	 then /bin/mv -f usage.dbk usage.dbk.old; \
	 fi
	$(GLM2DBKMS) -pdf usage.glm > usage.dbk

install.dbk: Makefile install.glm
	@if test -r install.dbk; \
	 then /bin/mv -f install.dbk install.dbk.old; \
	 fi
	$(GLM2DBKMS) -pdf install.glm > install.dbk

trouble.dbk: Makefile trouble.glm
	@if test -r trouble.dbk; \
	 then /bin/mv -f trouble.dbk trouble.dbk.old; \
	 fi
	$(GLM2DBKMS) -pdf trouble.glm > trouble.dbk

differences.dbk: Makefile differences.glm
	@if test -r differences.dbk; \
	 then /bin/mv -f differences.dbk differences.dbk.old; \
	 fi
	$(GLM2DBKMS) -pdf differences.glm > differences.dbk

grammar.dbk: Makefile grammar.glm
	@if test -r grammar.dbk; \
	 then /bin/mv -f grammar.dbk grammar.dbk.old; \
	 fi
	$(GLM2DBKGR) -pdf grammar.glm > grammar.dbk

libraries.dbk: Makefile libraries.glm
	@if test -r libraries.dbk; \
	 then /bin/mv -f libraries.dbk libraries.dbk.old; \
	 fi
	$(GLM2DBKMS) -pdf libraries.glm > libraries.dbk


bookinfo-htm.dbk: Makefile bookinfo.glm
	@if test -r bookinfo-htm.dbk; \
	 then /bin/mv -f bookinfo-htm.dbk bookinfo-htm.dbk.old; \
	 fi
	$(GLM2DBKMS) -htm bookinfo.glm > bookinfo-htm.dbk

disclaimer-htm.dbk: Makefile disclaimer.glm
	@if test -r disclaimer-htm.dbk; \
	 then /bin/mv -f disclaimer-htm.dbk disclaimer-htm.dbk.old; \
	 fi
	$(GLM2DBKMS) -htm disclaimer.glm > disclaimer-htm.dbk

intro-htm.dbk: Makefile intro.glm
	@if test -r intro-htm.dbk; \
	 then /bin/mv -f intro-htm.dbk intro-htm.dbk.old; \
	 fi
	$(GLM2DBKMS) -htm intro.glm > intro-htm.dbk

metaslang-htm.dbk: Makefile metaslang.glm
	@if test -r metaslang-htm.dbk; \
	 then /bin/mv -f metaslang-htm.dbk metaslang-htm.dbk.old; \
	 fi
	$(GLM2DBKMS) -htm metaslang.glm > metaslang-htm.dbk

usage-htm.dbk: Makefile usage.glm
	@if test -r usage-htm.dbk; \
	 then /bin/mv -f usage-htm.dbk usage-htm.dbk.old; \
	 fi
	$(GLM2DBKMS) -htm usage.glm > usage-htm.dbk

install-htm.dbk: Makefile install.glm
	@if test -r install-htm.dbk; \
	 then /bin/mv -f install-htm.dbk install-htm.dbk.old; \
	 fi
	$(GLM2DBKMS) -htm install.glm > install-htm.dbk

trouble-htm.dbk: Makefile trouble.glm
	@if test -r trouble-htm.dbk; \
	 then /bin/mv -f trouble-htm.dbk trouble-htm.dbk.old; \
	 fi
	$(GLM2DBKMS) -htm trouble.glm > trouble-htm.dbk

differences-htm.dbk: Makefile differences.glm
	@if test -r differences-htm.dbk; \
	 then /bin/mv -f differences-htm.dbk differences-htm.dbk.old; \
	 fi
	$(GLM2DBKMS) -htm differences.glm > differences-htm.dbk

grammar-htm.dbk: Makefile grammar.glm
	@if test -r grammar-htm.dbk; \
	 then /bin/mv -f grammar-htm.dbk grammar-htm.dbk.old; \
	 fi
	$(GLM2DBKGR) -htm grammar.glm > grammar-htm.dbk

libraries-htm.dbk: Makefile libraries.glm
	@if test -r libraries-htm.dbk; \
	 then /bin/mv -f libraries-htm.dbk libraries-htm.dbk.old; \
	 fi
	$(GLM2DBKMS) -htm libraries.glm > libraries-htm.dbk

grammar.glm: Makefile metaslang.glm grammar.preamble \
             bin/mkgrammar ~lambert/abc/meta/glmgramm.cmd
	@if test -r grammar.glm; \
	 then /bin/mv -f grammar.glm intro.dbk.old; \
	 fi
	bin/mkgrammar

clean:
	rm -rf $(PDFDBK) $(SLM).tex $(SLM).aux $(SLM).log \
	       $(SLM)-htm.dbk $(HTMDBK) *.old db2html-dir \
	       $(SLMDIR) $(SLMTAR) \

pristine: clean
	rm -rf $(SLMTARBOL)
