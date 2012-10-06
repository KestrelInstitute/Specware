all: pdf htm-zip

SUM= SpecwareIsabelleInterface

ARCH= i586
BIN= ../bin/$(ARCH)
GLM2DBK= $(BIN)/glm2dbk
SRC= ../src
GLM2DBKSRC= $(SRC)/glm2dbk.c

$(GLM2DBK): $(GLM2DBKSRC)
	cc -O $(GLM2DBKSRC) -o $(GLM2DBK)

pdf: $(SUM).pdf

DB2PDF= ../bin/db2pdf -E9999

PDFDBK= concepts.dbk usage.dbk

$(SUM).pdf: Makefile $(SUM).dbk $(PDFDBK)
	@if test -r $(SUM).pdf; \
	 then /bin/mv -f $(SUM).pdf $(SUM).pdf.old; \
	 fi
	($(DB2PDF) $(SUM).dbk 2>&1) | grep -v 'is not a function name' | tee jade.log

$(SUM).dbk: Makefile $(GLM2DBK) manual.dbk
	cp manual.dbk $(SUM).dbk

concepts.dbk: Makefile $(GLM2DBK) concepts.glm
	@if test -r concepts.dbk; \
	 then /bin/mv -f concepts.dbk concepts.dbk.old; \
	 fi
	$(GLM2DBK) -pdf concepts.glm > concepts.dbk

usage.dbk: Makefile $(GLM2DBK) usage.glm
	@if test -r usage.dbk; \
	 then /bin/mv -f usage.dbk usage.dbk.old; \
	 fi
	$(GLM2DBK) -pdf usage.glm > usage.dbk


HTMDIR= $(SUM).htm-dir

htm: $(HTMDIR)

htm-zip: htm
	rm -f $(HTMDIR).zip
	zip -r $(HTMDIR).zip $(HTMDIR)

DB2HTML= ../bin/db2html -E9999

ADJUSTFONTHTML= bin/adjustFontHTML

HTMDBK= concepts-htm.dbk  usage-htm.dbk

$(HTMDIR): Makefile $(SUM)-htm.dbk $(HTMDBK) $(ADJUSTFONTHTML)
	($(DB2HTML) $(SUM)-htm.dbk 2>&1) | grep -v 'is not a function name'
	/usr/bin/find db2html-dir -name '*.html' \
		-exec $(ADJUSTFONTHTML) {} \;
	/bin/mv db2html-dir/book1.html db2html-dir/$(SUM).html
	@/bin/rm -rf $(HTMDIR).old
	@if test -r $(HTMDIR); \
	 then /bin/mv -f $(HTMDIR) $(HTMDIR).old; \
	 fi
	/bin/mv db2html-dir $(HTMDIR)

$(SUM)-htm.dbk: Makefile $(GLM2DBK) $(SUM).dbk
	@if test -r $(SUM)-htm.dbk; \
	 then /bin/mv -f $(SUM)-htm.dbk $(SUM)-htm.dbk.old; \
	 fi
	sed 's/.dbk/-htm.dbk/g' $(SUM).dbk > $(SUM)-htm.dbk

concepts-htm.dbk: Makefile $(GLM2DBK) concepts.glm
	@if test -r concepts-htm.dbk; \
	 then /bin/mv -f concepts-htm.dbk concepts-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm concepts.glm > concepts-htm.dbk

usage-htm.dbk: Makefile $(GLM2DBK) usage.glm
	@if test -r usage-htm.dbk; \
	 then /bin/mv -f usage-htm.dbk usage-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm usage.glm > usage-htm.dbk

clean:
	rm -rf $(SUM).tex $(SUM).aux $(SUM).log $(SUM).out \
	$(PDFDBK) $(HTMDBK) $(HTMDIR) *.old \
	$(SUM).dbk $(SUM)-htm.dbk jade.log

pristine: clean

