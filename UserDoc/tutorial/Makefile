all: pdf

ST= SpecwareTutorial

pdf: $(ST).pdf

ARCH= i586
BIN= ../bin/$(ARCH)
GLM2DBKMS= $(BIN)/glm2dbk -metaslang

DB2PDF= ../bin/db2pdf -E9999

PDFDBK= concepts.dbk install.dbk example.dbk

$(ST).dbk: Makefile tutorial.dbk
	cp tutorial.dbk $(ST).dbk

concepts.dbk: Makefile concepts.glm
	@if test -r concepts.dbk; \
	 then /bin/mv -f concepts.dbk concepts.dbk.old; \
	 fi
	$(GLM2DBKMS) -pdf concepts.glm > concepts.dbk

install.dbk: Makefile install.glm
	@if test -r install.dbk; \
	 then /bin/mv -f install.dbk install.dbk.old; \
	 fi
	$(GLM2DBKMS) -pdf install.glm > install.dbk

example.dbk: Makefile example.glm
	@if test -r example.dbk; \
	 then /bin/mv -f example.dbk example.dbk.old; \
	 fi
	$(GLM2DBKMS) -pdf example.glm > example.dbk

$(ST).pdf: Makefile $(ST).dbk $(PDFDBK)
	@if test -r $(ST).pdf; \
	 then /bin/mv -f $(ST).pdf $(ST).pdf.old; \
	 fi
	($(DB2PDF) $(ST).dbk 2>&1) | grep -v 'is not a function name' | tee jade.log

zip: pdfservice.zip

pdfservice.zip: $(ST).pdf SpecwareTutorial.pdf tutorial.dbk concepts.glm install.glm example.glm jade.log
	rm -f pdfservice.zip
	zip pdfservice.zip SpecwareTutorial.pdf tutorial.dbk concepts.glm install.glm example.glm

clean:
	rm -rf $(ST).tex $(ST).aux $(ST).log
