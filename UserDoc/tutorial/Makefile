all: pdf htm-zip

ST= SpecwareTutorial

ARCH= i586
BIN= ../bin/$(ARCH)
GLM2DBK= $(BIN)/glm2dbk

pdf: $(ST).pdf

DB2PDF= ../bin/db2pdf -E9999

PDFDBK= concepts.dbk example.dbk

$(ST).pdf: Makefile $(ST).dbk $(PDFDBK)
	@if test -r $(ST).pdf; \
	 then /bin/mv -f $(ST).pdf $(ST).pdf.old; \
	 fi
	($(DB2PDF) $(ST).dbk 2>&1) | grep -v 'is not a function name' | tee jade.log

$(ST).dbk: Makefile $(GLM2DBK) tutorial.dbk
	cp tutorial.dbk $(ST).dbk

concepts.dbk: Makefile $(GLM2DBK) concepts.glm
	@if test -r concepts.dbk; \
	 then /bin/mv -f concepts.dbk concepts.dbk.old; \
	 fi
	$(GLM2DBK) -pdf concepts.glm > concepts.dbk

example.dbk: Makefile $(GLM2DBK) example.glm
	@if test -r example.dbk; \
	 then /bin/mv -f example.dbk example.dbk.old; \
	 fi
	$(GLM2DBK) -pdf example.glm > example.dbk

HTMDIR= $(ST).htm-dir

htm: $(HTMDIR)

htm-zip: htm
	rm -f $(HTMDIR).zip
	zip -r $(HTMDIR).zip $(HTMDIR)

DB2HTML= ../bin/db2html -E9999

ADJUSTFONTHTML= bin/adjustFontHTML

HTMDBK= concepts-htm.dbk example-htm.dbk

$(HTMDIR): Makefile $(ST)-htm.dbk $(HTMDBK) $(ADJUSTFONTHTML)
	($(DB2HTML) $(ST)-htm.dbk 2>&1) | grep -v 'is not a function name'
	/usr/bin/find db2html-dir -name '*.html' \
		-exec $(ADJUSTFONTHTML) {} \;
	/bin/mv db2html-dir/book1.html db2html-dir/$(ST).html
	@/bin/rm -rf $(HTMDIR).old
	@if test -r $(HTMDIR); \
	 then /bin/mv -f $(HTMDIR) $(HTMDIR).old; \
	 fi
	/bin/mv db2html-dir $(HTMDIR)

$(ST)-htm.dbk: Makefile $(GLM2DBK) $(ST).dbk
	@if test -r $(ST)-htm.dbk; \
	 then /bin/mv -f $(ST)-htm.dbk $(ST)-htm.dbk.old; \
	 fi
	sed 's/.dbk/-htm.dbk/g' $(ST).dbk > $(ST)-htm.dbk

concepts-htm.dbk: Makefile $(GLM2DBK) concepts.glm
	@if test -r concepts-htm.dbk; \
	 then /bin/mv -f concepts-htm.dbk concepts-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm concepts.glm > concepts-htm.dbk

example-htm.dbk: Makefile $(GLM2DBK) example.glm
	@if test -r example-htm.dbk; \
	 then /bin/mv -f example-htm.dbk example-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm example.glm > example-htm.dbk

clean:
	rm -rf $(ST).tex $(ST).aux $(ST).log $(ST).out \
	$(PDFDBK) $(HTMDBK) *.old $(ST).htm-dir \
	$(ST).dbk $(ST)-htm.dbk jade.log

pristine: clean
