all: pdf htm-zip

SUM= SpecwareUserManual

ARCH= i586
BIN= ../bin/$(ARCH)
GLM2DBK= $(BIN)/glm2dbk
SRC= ../src
GLM2DBKSRC= $(SRC)/glm2dbk.c

$(GLM2DBK): $(GLM2DBKSRC)
	cc -O $(GLM2DBKSRC) -o $(GLM2DBK)

pdf: $(SUM).pdf

DB2PDF= ../bin/db2pdf -E9999

PDFDBK= debug.dbk defining.dbk emacs.dbk generatedlisp.dbk \
  install.dbk model.dbk process.dbk prove.dbk start.dbk \
  javacodegen.dbk ccodegen.dbk

$(SUM).pdf: Makefile $(SUM).dbk $(PDFDBK)
	@if test -r $(SUM).pdf; \
	 then /bin/mv -f $(SUM).pdf $(SUM).pdf.old; \
	 fi
	($(DB2PDF) $(SUM).dbk 2>&1) | grep -v 'is not a function name' | tee jade.log

$(SUM).dbk: Makefile $(GLM2DBK) manual.dbk
	cp manual.dbk $(SUM).dbk

debug.dbk: Makefile $(GLM2DBK) debug.glm
	@if test -r debug.dbk; \
	 then /bin/mv -f debug.dbk debug.dbk.old; \
	 fi
	$(GLM2DBK) -pdf debug.glm > debug.dbk

defining.dbk: Makefile $(GLM2DBK) defining.glm
	@if test -r defining.dbk; \
	 then /bin/mv -f defining.dbk defining.dbk.old; \
	 fi
	$(GLM2DBK) -pdf defining.glm > defining.dbk

emacs.dbk: Makefile $(GLM2DBK) emacs.glm
	@if test -r emacs.dbk; \
	 then /bin/mv -f emacs.dbk emacs.dbk.old; \
	 fi
	$(GLM2DBK) -pdf emacs.glm > emacs.dbk

generatedlisp.dbk: Makefile $(GLM2DBK) generatedlisp.glm
	@if test -r generatedlisp.dbk; \
	 then /bin/mv -f generatedlisp.dbk generatedlisp.dbk.old; \
	 fi
	$(GLM2DBK) -pdf generatedlisp.glm > generatedlisp.dbk

install.dbk: Makefile $(GLM2DBK) install.glm
	@if test -r install.dbk; \
	 then /bin/mv -f install.dbk install.dbk.old; \
	 fi
	$(GLM2DBK) -pdf install.glm > install.dbk

model.dbk: Makefile $(GLM2DBK) model.glm
	@if test -r model.dbk; \
	 then /bin/mv -f model.dbk model.dbk.old; \
	 fi
	$(GLM2DBK) -pdf model.glm > model.dbk

process.dbk: Makefile $(GLM2DBK) process.glm
	@if test -r process.dbk; \
	 then /bin/mv -f process.dbk process.dbk.old; \
	 fi
	$(GLM2DBK) -pdf process.glm > process.dbk

prove.dbk: Makefile $(GLM2DBK) prove.glm
	@if test -r prove.dbk; \
	 then /bin/mv -f prove.dbk prove.dbk.old; \
	 fi
	$(GLM2DBK) -pdf prove.glm > prove.dbk

start.dbk: Makefile $(GLM2DBK) start.glm
	@if test -r start.dbk; \
	 then /bin/mv -f start.dbk start.dbk.old; \
	 fi
	$(GLM2DBK) -pdf start.glm > start.dbk

javacodegen.dbk: Makefile $(GLM2DBK) javacodegen.glm
	@if test -r javacodegen.dbk; \
	 then /bin/mv -f javacodegen.dbk javacodegen.dbk.old; \
	 fi
	$(GLM2DBK) -pdf javacodegen.glm > javacodegen.dbk

ccodegen.dbk: Makefile $(GLM2DBK) ccodegen.glm
	@if test -r ccodegen.dbk; \
	 then /bin/mv -f ccodegen.dbk ccodegen.dbk.old; \
	 fi
	$(GLM2DBK) -pdf ccodegen.glm > ccodegen.dbk

HTMDIR= $(SUM).htm-dir

htm: $(HTMDIR)

htm-zip: htm
	rm -f $(HTMDIR).zip
	zip -r $(HTMDIR).zip $(HTMDIR)

DB2HTML= ../bin/db2html -E9999

ADJUSTFONTHTML= bin/adjustFontHTML

HTMDBK= debug-htm.dbk defining-htm.dbk emacs-htm.dbk generatedlisp-htm.dbk \
  install-htm.dbk model-htm.dbk process-htm.dbk prove-htm.dbk start-htm.dbk

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

debug-htm.dbk: Makefile $(GLM2DBK) debug.glm
	@if test -r debug-htm.dbk; \
	 then /bin/mv -f debug-htm.dbk debug-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm debug.glm > debug-htm.dbk

defining-htm.dbk: Makefile $(GLM2DBK) defining.glm
	@if test -r defining-htm.dbk; \
	 then /bin/mv -f defining-htm.dbk defining-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm defining.glm > defining-htm.dbk

emacs-htm.dbk: Makefile $(GLM2DBK) emacs.glm
	@if test -r emacs-htm.dbk; \
	 then /bin/mv -f emacs-htm.dbk emacs-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm emacs.glm > emacs-htm.dbk

generatedlisp-htm.dbk: Makefile $(GLM2DBK) generatedlisp.glm
	@if test -r generatedlisp-htm.dbk; \
	 then /bin/mv -f generatedlisp-htm.dbk generatedlisp-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm generatedlisp.glm > generatedlisp-htm.dbk

install-htm.dbk: Makefile $(GLM2DBK) install.glm
	@if test -r install-htm.dbk; \
	 then /bin/mv -f install-htm.dbk install-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm install.glm > install-htm.dbk

model-htm.dbk: Makefile $(GLM2DBK) model.glm
	@if test -r model-htm.dbk; \
	 then /bin/mv -f model-htm.dbk model-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm model.glm > model-htm.dbk

process-htm.dbk: Makefile $(GLM2DBK) process.glm
	@if test -r process-htm.dbk; \
	 then /bin/mv -f process-htm.dbk process-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm process.glm > process-htm.dbk

prove-htm.dbk: Makefile $(GLM2DBK) prove.glm
	@if test -r prove-htm.dbk; \
	 then /bin/mv -f prove-htm.dbk prove-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm prove.glm > prove-htm.dbk

start-htm.dbk: Makefile $(GLM2DBK) start.glm
	@if test -r start-htm.dbk; \
	 then /bin/mv -f start-htm.dbk start-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm start.glm > start-htm.dbk

javacodegen-htm.dbk: Makefile $(GLM2DBK) javacodegen.glm
	@if test -r javacodegen-htm.dbk; \
	 then /bin/mv -f javacodegen-htm.dbk javacodegen-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm javacodegen.glm > javacodegen-htm.dbk

ccodegen-htm.dbk: Makefile $(GLM2DBK) ccodegen.glm
	@if test -r ccodegen-htm.dbk; \
	 then /bin/mv -f ccodegen-htm.dbk ccodegen-htm.dbk.old; \
	 fi
	$(GLM2DBK) -htm ccodegen.glm > ccodegen-htm.dbk

clean:
	rm -rf $(SUM).tex $(SUM).aux $(SUM).log $(SUM).out \
	$(PDFDBK) $(HTMDBK) $(HTMDIR) *.old \
	$(SUM).dbk $(SUM)-htm.dbk jade.log

pristine: clean

