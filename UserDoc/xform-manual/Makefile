all: pdf htm-zip

SXM= SpecwareXformManual

BIN= ../bin
GLM2DBK= $(BIN)/glm2dbk.o
SRC= ../src
GLM2DBKSRC= $(SRC)/glm2dbk.c

$(GLM2DBK): $(GLM2DBKSRC)
	gcc $(GLM2DBKSRC) -o $(GLM2DBK)

pdf: $(SXM).pdf

DB2PDF= ../bin/db2pdf -E9999

PDFDBK= intro.dbk xshell.dbk iso.dbk

$(SXM).pdf: Makefile $(SXM).dbk $(PDFDBK)
	@if test -r $(SXM).pdf; \
	 then mv -f $(SXM).pdf $(SXM).pdf.old; \
	 fi
	($(DB2PDF) $(SXM).dbk 2>&1) | grep -v 'is not a function name' | tee jade.log

$(SXM).dbk: Makefile $(GLM2DBK) xmanual.dbk
	cp xmanual.dbk $(SXM).dbk

intro.dbk: Makefile $(GLM2DBK) intro.glm
	@if test -r intro.dbk; \
	 then mv -f intro.dbk intro.dbk.old; \
	 fi
	$(GLM2DBK) -pdf intro.glm > intro.dbk

xshell.dbk: Makefile $(GLM2DBK) xshell.glm
	@if test -r xshell.dbk; \
	 then mv -f xshell.dbk xshell.dbk.old; \
	 fi
	$(GLM2DBK) -pdf xshell.glm > xshell.dbk

iso.dbk: Makefile $(GLM2DBK) iso.glm
	@if test -r iso.dbk; \
	 then mv -f iso.dbk iso.dbk.old; \
	 fi
	$(GLM2DBK) -pdf iso.glm > iso.dbk

HTMDIR= $(SXM).htm-dir

htm: $(HTMDIR)

htm-zip: htm
	rm -f $(HTMDIR).zip
	zip -r $(HTMDIR).zip $(HTMDIR)

DB2HTML= ../bin/db2html -E9999

ADJUSTFONTHTML= bin/adjustFontHTML

HTMDBK= intro-htm.dbk xshell-htm.dbk iso-htm.dbk

$(HTMDIR): Makefile $(SXM)-htm.dbk $(HTMDBK) $(ADJUSTFONTHTML)
	($(DB2HTML) $(SXM)-htm.dbk 2>&1) | grep -v 'is not a function name'
	find db2html-dir -name '*.html' \
		-exec $(ADJUSTFONTHTML) {} \;
	mv db2html-dir/book1.html db2html-dir/$(SXM).html
	@rm -rf $(HTMDIR).old
	@if test -r $(HTMDIR); \
	 then mv -f $(HTMDIR) $(HTMDIR).old; \
	 fi
	mv db2html-dir $(HTMDIR)

$(SXM)-htm.dbk: Makefile $(GLM2DBK) $(SXM).dbk
	@if test -r $(SXM)-htm.dbk; \
	 then mv -f $(SXM)-htm.dbk $(SXM)-htm.dbk.old; \
	 fi
	sed 's/.dbk/-htm.dbk/g' $(SXM).dbk > $(SXM)-htm.dbk

intro-htm.dbk: Makefile $(GLM2DBK) intro.glm
	@if test -r intro-htm.dbk; \
	 then mv -f intro-htm.dbk intro-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm intro.glm > intro-htm.dbk

xshell-htm.dbk: Makefile $(GLM2DBK) xshell.glm
	@if test -r xshell-htm.dbk; \
	 then mv -f xshell-htm.dbk xshell-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm xshell.glm > xshell-htm.dbk

iso-htm.dbk: Makefile $(GLM2DBK) iso.glm
	@if test -r iso-htm.dbk; \
	 then mv -f iso-htm.dbk iso-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm iso.glm > iso-htm.dbk

clean:
	rm -rf $(SXM).tex $(SXM).aux $(SXM).log $(SXM).out \
	$(PDFDBK) $(HTMDBK) $(HTMDIR) *.old \
	$(SXM).dbk $(SXM)-htm.dbk jade.log $(HTMDIR).zip $(SXM).pdf

pristine: clean

