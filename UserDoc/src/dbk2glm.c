#define TRACING 0
#define trace(a) if(TRACING)printf(a)
#define trace2(a,b) if(TRACING)printf(a,b)
#define trace3(a,b,c) if(TRACING)printf(a,b,c)
#define trace4(a,b,c,d) if(TRACING)printf(a,b,c,d)

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <ctype.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

typedef int bool;
#define True (1)
#define False (0)
#define succeed return True
#define fail    return False

int argc, argi; char **argv;

int fstck= 0;
FILE *fstr[99];
char *fname[99];
int flino[99];
bool saw_nl[99];
#define this(a) a[fstck-1]
#define is_stdin(name) (name[0] == '-' && !name[1])

bool pushf(pname) char* pname; {
	fstck++;
	if (fstck == 1 && is_stdin(pname))
		this(fstr)= stdin;
	else
		this(fstr)= fopen(pname, "r");
	if (this(fstr) == (FILE *) NULL) {
		fstck--;
		globmess3("Could not open file `", pname, "'");
		return 0;
	}
	this(fname)= pname;
	this(flino)= 0;
	this(saw_nl)= True;
	succeed;
}

popf() {
	if (fstck) {
		if (!is_stdin(this(fname))) fclose(this(fstr));
		fstck--;
	}
}

int gtchar() {
	int k;

	if (argi >= argc) return EOF;

	if (argi < 0) {
		argi++;
		if (argc == 1)
			(void) pushf("-");
		else
			if (!pushf(argv[++argi])) return EOF;
	}

	while ((k= getc(this(fstr))) == EOF) {
		popf();
		if (++argi >= argc || !pushf(argv[argi])) return EOF;
	}

	this(flino)+= this(saw_nl);
	this(saw_nl)= k == '\n';
	return k;
}

check_rdable() {
	fstck= 0;
	(void) pushf(argv[argi]);
	popf(argv[argi]);
}


w22(s) char *s; {
	write(2, s, (unsigned) strlen(s));
}

bool KO= False;

#define LOCAL 'L'
#define GLOBAL 'G'
char linodec[99];
mess3(scope, s0, s1, s2) char scope, *s0, *s1, *s2; {
	KO= True;
	w22(argv[0]); w22(": ");
	if (scope == LOCAL && fstck) {
		if (this(fstr) != stdin) {
			w22("input file `");
			w22(this(fname));
			w22("', ");
		}
		else if (argc > 1)
			w22("stdin, ");
		sprintf(linodec, "line %d: ", this(flino));
		w22(linodec);
	}
	w22(s0); w22(s1); w22(s2); w22("\n");
}

locmess3(s0, s1, s2) char *s0, *s1, *s2; {
	mess3(LOCAL, s0, s1, s2);
}

globmess3(s0, s1, s2) char *s0, *s1, *s2; {
	mess3(GLOBAL, s0, s1, s2);
}

locmess(s) char *s; {
	locmess3(s, "", "");
}

globmess(s) char *s; {
	globmess3(s, "", "");
}

main(main_argc, main_argv) int main_argc; char **main_argv; {
	argc= main_argc; argv= main_argv;

	for (argi= 1; argi < argc; argi++)
		check_rdable();
	if (KO) return KO;

	argi= -1;
	process();
	return KO;
}

#define BUFSIZE (1<<23)
char buf[BUFSIZE];
long bufp, bufq;

#define BBuf(p) (buf[((p)+BUFSIZE)%BUFSIZE])
#define Buf(p) (buf[(p)])

#define EOT '\0'

#define atEOT (thischar() == EOT)

#define atBOL (bufp == 0 || lastchar() == '\n')
#define atEOL (atEOT || thischar() == '\n')

#define getchar GETCHAR

char getchar() {
	int k;

	while (bufp >= bufq) {
		k= gtchar();
		Buf(bufq++)= k == EOF ? EOT : k;
	}

	return Buf(bufp++);
}

char thischar() {
	long bp= bufp; char c;
	
	c= getchar();
	bufp= bp;
	return c;
}

char nextchar() {
	long bp= bufp; char c;
	
	c= getchar();
	c= getchar();
	bufp= bp;
	return c;
}

char lastchar() {
	if (bufp < 1) return EOT;
	return Buf(bufp-1);
}

char prelastchar() {
	if (bufp < 2) return EOT;
	return Buf(bufp-2);
}

bool seechar(c) {
	long bp= bufp;
trace3("{{%c@%c:", c, atEOT ? '?' : Buf(bufp));
	if (getchar() == c)
{ trace("+}}");
				succeed;
} trace("-}}");
	bufp= bp;
	fail;
}

skip(cc) char* cc; {
	char c, *cp;

	do {
		if (!(c= getchar())) return;
trace2("$$%c", c);
		for (cp= cc; *cp; cp++)
			if (c == *cp) continue;
		bufp--;
		return;
	} while (True);
}

seek(cc) char* cc; {
	char c, *cp;

	do {
		if (!(c= getchar())) return;
trace2("$%c", c);
		for (cp= cc; *cp; cp++)
			if (c == *cp) return;
	} while (True);
}

#define isalnumhyp(c) (isalnum(c) || c == '-')

bool seetext(t) char *t; {
	long bp= bufp;

	if (isalnum(thischar()) && isalnumhyp(lastchar())) fail;
trace2("?(%s)", t);
	while (*t) {
		if (!seechar(*t++)) {
			bufp= bp;
			fail;
		}
	}
	if (thischar() == '-' && nextchar() == '>') {
trace("!()");
		succeed;
	}
	if (isalnumhyp(thischar()) && isalnum(lastchar())) {
			bufp= bp;
			fail;
	}
trace2("!(%s)", t);
	succeed;
}

bool inCData= False;
bool inProgram= False;
bool inSyntax= False;
#define inProgramOrSyntax (inProgram || inSyntax)
bool inDisplay= False;
bool inFilename= False;

outchar(c) char c; {
trace(" ");
	putchar(c);
trace(" ");
}

outtext(t) char *t; {
	while (*t) outchar(*t++);
}

char tokkey[9999][99], tokass[9999][999];
int tokdown[9999];
int tokp= 0;

tokdef() {
	int wp;

	if (atEOT) fail;
trace("\ntokdef:: ");
	if (!(atBOL && seetext("== "))) fail;

        skip(" ");

	wp= 0;
	while (!(atEOL || seechar(' ') || seechar('\t'))) {
		tokkey[tokp][wp++]= getchar();
	}
	tokkey[tokp][wp]= '\0';

        while (seechar(' ') || seechar('\t'));

	wp= 0;
	while (!(atEOL || seechar(' ') || seechar('\t'))) {
		tokass[tokp][wp++]= getchar();
	}
	tokass[tokp][wp]= '\0';
trace3(" so %s |> %s ", tokkey[tokp], tokass[tokp]);

        while (seechar(' ') || seechar('\t'));

	tokdown[tokp]= tokp;
	bubble_up();
	tokp++;
	putchar('%');

	succeed;
}

bubble_up() {
	int len= strlen(tokkey[tokp]), p;

if (0||TRACING) showtokk();
	p= tokp-1;
	while (p >= 0 && strlen(tokkey[tokdown[p]]) < len) {
		tokdown[p+1]= tokdown[p];
		tokdown[p]= tokp;
		p--;
	}
if (0||TRACING) showtokk();
}

showtokk() {
	int p;
	putchar('\n');
	for (p= 0; p <= tokp; p++)
	printf("%s |-> %s\n", tokkey[tokdown[p]], tokass[tokdown[p]]);
}

token() {
	int p;
	if (atEOT) fail;
trace("\ntoken:: ");

	for (p= 0; p < tokp; p++)
	if (seetext(tokkey[tokdown[p]])) {
		outtext("BRULF");
		outtext(tokass[tokdown[p]]);
		outchar("FLURB");
		succeed;
	}

	fail;
}

#define try(f) if (f()) continue

/***************************************************************************/

bool didII= False;

process() {
	int k;

	while (!atEOT) {
trace3("P%d%c\n", bufp,thischar());
		try(program);
		try(outProgram);
		try(syntax);
		try(outSyntax);
		try(cData);
		try(outCData);

		try(nlDisplay);
		didII= False;

		try(moreCData);
		try(filename);
		try(outFilename);

		try(nonterminal);
		try(syntaxOperator);
		try(terminal);

		try(ent);
		other();
	}
}

bool program() {
	bool ipl= False;

	if (inProgram) fail;
trace("\nprogram:: ");
	if (!((ipl= seetext("<programlisting")) || seetext("<computeroutput"))) fail;
	outtext("[[");
	skip(" \n");
	if (seetext ("lang=\"lisp\"")) outtext("L:");
	seek(">");
if (atEOT) trace("BOO\n");
	inProgram= True;
	inDisplay= ipl;
	succeed;
}

bool outProgram() {
	if (!inProgram) fail;
trace("\noutProgram:: ");
	if (!(seetext("</programlisting>") || seetext("</computeroutput>"))) fail;
	outtext("]]");
	inProgram= inDisplay= False;
	succeed;
}

bool syntax() {
	bool ipl= False;

	if (inSyntax) fail;
trace("\nsyntax:: ");
	if (!((ipl= seetext("<programlistinG")) || seetext("<computeroutpuT"))) fail;
	outtext("<<");
	skip(" \n");
	seek(">");
if (atEOT) trace("BOO\n");
	inSyntax= True;
	inDisplay= ipl;
	succeed;
}

bool outSyntax() {
	if (!inSyntax) fail;
trace("\noutSyntax:: ");
	if (!(seetext("</programlistinG>") || seetext("</computeroutpuT>"))) fail;
	outtext(">>");
	inSyntax= inDisplay= False;
	succeed;
}

bool nlDisplay() {
	if (!inDisplay || didII) fail;
trace("\nnlDisplay:: ");
	if (!atBOL) fail;
	if (thischar() != '|') outtext("||");
	didII= True;
	succeed;
}

bool cData() {
	if (inCData) fail;
trace("\ncData:: ");
	if (!seetext ("<![CDATA[")) fail;
	inCData= True;
	succeed;
}

bool outCData() {
	if (!inCData) fail;
trace("\noutCData:: ");
	if (!seetext("]]>")) fail;
	inCData= False;
	succeed;
}

bool moreCData() {
	if (!inCData) fail;
trace("\nmoreCData:: ");
	other();
	succeed;
}

bool filename() {
	if (inFilename) fail;
trace("\nfilename:: ");
	if (!seetext("<filename>")) fail;
	outtext("<\"");
	inFilename= True;
	succeed;
}

bool outFilename() {
	if (!inFilename) fail;
trace("\noutFilename:: ");
	if (!seetext("</filename>")) fail;
	outtext("\">");
	inFilename= False;
	succeed;
}

bool nonterminal() {
	char c;

	if (!(seetext("<guimenU role=\"nonterminal\">") ||
	      seetext("<parameteR role=\"nonterminal\">"))) fail;
trace("\nnonterminal:: ");
	outchar('`');
	while (!(seetext("</guimenU>") || seetext("</parameteR>")))
		outchar(getchar());
	succeed;
}

bool syntaxOperator() {
	if (!inSyntax) fail;
trace("\nsyntaxOperator:: ");
	if (seechar(' ')) {
		outchar(' ');
		succeed;
	}
	if (seechar('\n')) {
		outchar('\n');
		succeed;
	}
	if (seetext("::=")) {
		outtext("::=");
		succeed;
	}
	if (seechar('|')) {
		outchar('|');
		succeed;
	}
	if (seechar('{')) {
		outchar('{');
		succeed;
	}
	if (seetext("}*")) {
		outtext("}*");
		succeed;
	}
	if (seechar('[')) {
		outchar('[');
		succeed;
	}
	if (seechar(']')) {
		outchar(']');
		succeed;
	}
	fail;
}

bool terminal() {
	char c;

	if (!inSyntax) fail;
trace("\nterminal:: ");
	if (seetext("</userinpuT>")) succeed;

        seetext("<userinpuT role=\"terminal\">");
	if (seetext("</userinpuT>")) succeed;

	if (seechar('\'')) {
		outtext("''");
		succeed;
	}
	if (seetext("::=")) {
		outtext("'::=");
		succeed;
	}
	if (seechar('|')) {
		outtext("'|");
		succeed;
	}
	if (seechar('{')) {
		outtext("'{");
		succeed;
	}
	if (seetext("}*")) {
		outtext("'}*");
		succeed;
	}
	if (seechar('}')) {
		outtext("'}");
		succeed;
	}
	if (seechar('[')) {
		outtext("'[");
		succeed;
	}
	if (seechar(']')) {
		outtext("']");
		succeed;
	}
	fail;
}

bool ent() {
	if (!inProgramOrSyntax) fail;
trace("\nent:: ");
	if (seetext("&lt;") || seetext("&#60;")) {
		outtext("<");
		succeed;
	}
	if (seetext("&gt;") || seetext("&#62;")) {
		outtext(">");
		succeed;
	}
	if (seetext("&amp;")) {
		outtext("&");
		succeed;
	}
	if (seetext("<")) {
		outtext("\\<");
		succeed;
	}
	if (seetext(">")) {
		outtext(">");
		succeed;
	}
	fail;
}

bool other() {
trace("\nother:: ");
	outchar(getchar());
	succeed;
}
