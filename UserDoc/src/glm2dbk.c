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

bool html= True;

#define NONTERMINAL (html ? "parameteR" : "guimenU")

bool linking= False, grlinking= False;

main(main_argc, main_argv) int main_argc; char **main_argv; {

	if (main_argc > 1 && main_argv[1][0] == '-' &&
	    (main_argv[1][1] == 'm' || main_argv[1][1] == 'g')) {
		linking= True;
	    	grlinking= main_argv[1][1] == 'g';
		main_argv++; main_argc--;
	}

	if (main_argc > 1 && main_argv[1][0] == '-' &&
	    (main_argv[1][1] == 'h' || main_argv[1][1] == 'p')) {
	    	html= main_argv[1][1] == 'h';
		main_argv++; main_argc--;
	}

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

backchar() {
	bufp--;
}

skip(cc) char* cc; {
	char c, *cp;

	do {
		if (!(c= getchar())) return;
		for (cp= cc; *cp; cp++)
			if (c == *cp) break;
		return;
	} while (True);
	backchar();
}

seek(cc) char* cc; {
	char c, *cp;

	do {
		if (!(c= getchar())) return;
		for (cp= cc; *cp; cp++)
			if (c == *cp) return;
	} while (True);
}

#define isalnumhyp(c) (isalnum((c)) || (c) == '-')

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

bool aheadtext(t) char *t; {
	long bp= bufp;

	if (isalnum(thischar()) && isalnumhyp(lastchar())) fail;
trace2("??(%s)", t);
	while (*t) {
		if (!seechar(*t++)) {
			bufp= bp;
			fail;
		}
	}
	bufp= bp;
	if (thischar() == '-' && nextchar() == '>') {
trace("!()");
		succeed;
	}
	if (isalnumhyp(thischar()) && isalnum(lastchar()))
		fail;
trace2("!(%s)", t);
	succeed;
}

bool inCData= False;
bool inProgram= False;
bool inSyntax= False;
#define inProgramOrSyntax (inProgram || inSyntax)
bool inDisplay= False;
bool inTerminal= False;
bool inFilename= False;
bool inQuote= False;

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

process() {
	int k;

	while (!atEOT) {
trace3("P%d%c\n", bufp,thischar());
		try(program);
		try(outProgram);
		try(syntax);
		try(outSyntax);

		try(nlDisplay);

		try(filename);
		try(outFilename);

		try(nonterminal);
		try(syntaxOperator);
		try(terminal);

		try(dollar);
		try(replaceable);
		try(ent);
		try(quote);
		try(outQuote);
		other();
	}
}

bool program() {
	bool ipl= atBOL, lisp= False;

	if (inProgramOrSyntax) fail;
trace("\nprogram:: ");
	if (!seetext("[[")) fail;
	lisp= seetext("L:");
	ipl&= atEOL;
	inProgram= True;
	inDisplay= ipl;
	if (inDisplay) outtext("<programlisting lang=");
	else outtext("<computeroutput lang=");
	if (lisp) outtext("\"lisp\">");
	else outtext("\"metaslang\">");
	succeed;
}

bool outProgram() {
	if (!inProgramOrSyntax) fail;
trace("\noutProgram:: ");
	if (!seetext("]]")) fail;
	while (seechar(']')) outchar(']');
	if (inDisplay) outtext("</programlisting>");
	else outtext("</computeroutput>");
	inProgram= inDisplay= False;
	succeed;
}

bool syntax() {
	bool ipl= atBOL;

	if (inProgramOrSyntax) fail;
trace("\nsyntax:: ");
	if (!seetext("<<")) fail;
	ipl&= atEOL;
	inSyntax= True;
	inDisplay= ipl;
	if (inDisplay) outtext("<programlistinG lang=");
	else outtext("<computeroutpuT lang=");
	outtext("\"syntax\">");
	succeed;
}

bool outSyntax() {
	if (!inSyntax) fail;
trace("\noutSyntax:: ");
	if (!seetext(">>")) fail;
	while (seechar('>')) {
		backchar();
		terminal();
	}
	exitTerminal();
	if (inDisplay) outtext("</programlistinG>");
	else outtext("</computeroutpuT>");
	inSyntax= inDisplay= False;
	succeed;
}

bool nlDisplay() {
	if (!inDisplay) fail;
trace("\nnlDisplay:: ");
	if (!atBOL) fail;
	if (!seechar('|')) fail;
	skip("|");
	succeed;
}

bool filename() {
	if (inFilename) fail;
trace("\nfilename:: ");
	if (!seetext("<\"")) fail;
	outtext("<filename>");
	inFilename= True;
	succeed;
}

bool outFilename() {
	if (!inFilename) fail;
trace("\noutFilename:: ");
	if (!seetext("\">")) fail;
	outtext("</filename>");
	inFilename= False;
	succeed;
}

char nt[999], NTR[999];
int ntp, NTRp;

getnt() {
	char c;

	ntp= NTRp= 0;
	c= getchar();
	while (isalnumhyp(c)) {
		nt[ntp++]= c;
		NTR[NTRp++]= tolower(c);
		c= getchar();
	}
	backchar();
	nt[ntp]= NTR[NTRp]= '\0';

	if ((nt[0] == 'w' || nt[0] == 'p')
	 && (nt[1] == 'i' || nt[1] == 'a')
	 && nt[2] == 'f' && nt[3] == 'f' && nt[4] == 'l' && nt[5] == 'e') {
		NTRp= 0;
	}

	if (nt[ntp-1] == '-') {
		NTRp= 0;
	}

	if (NTRp && NTR[NTRp-1] == 's') {
		NTR[--NTRp]= '\0';
		if (NTR[NTRp-2] == 'h' && NTR[NTRp-1] == 'e')
			NTR[--NTRp]= '\0';
	}
}

putnt() {
	outtext(nt);
}

putNTR() {
	outtext(NTR);
}

preanchor(c) char *c; {
	if (!linking || !NTRp) return;
	outtext("<phrase id=\"");
	outtext(c); outchar('-'); putNTR();
	outtext("\">");
}

postanchor() {
	if (!linking || !NTRp) return;
	outtext("</phrase>");
}

prelink(c) char *c; {
	if (!linking || !NTRp) return;
	outtext("<link linkend=\"");
	outtext(c); outchar('-'); putNTR();
	outtext("\">");
}

postlink() {
	if (!linking || !NTRp) return;
	outtext("</link>");
}

bool nonterminal() {
	bool isdefn;

	if (!(thischar() == '`' &&
		isalpha(nextchar()) && isalpha(nextchar()))) fail;
	if (!seechar('`')) fail;
trace("\nnonterminal:: ");
	exitTerminal();

	getnt();
	isdefn= aheadtext(" ::=");

	if (isdefn) {
		preanchor(grlinking ? "grammar" : "metaslang");
		if (grlinking) prelink("metaslang");
	} else
		prelink(grlinking ? "grammar" : "metaslang");

	outtext("<"); outtext(NONTERMINAL); outtext(" role=\"nonterminal\">");
	putnt();
	outtext("</"); outtext(NONTERMINAL); outtext(">");
	if (isdefn) {
		if (grlinking) postlink();
		postanchor();
	} else
		postlink();
	succeed;
}

bool syntaxOperator() {
	if (!inSyntax) fail;
trace("\nsyntaxOperator:: ");
	if (seechar(' ')) {
		exitTerminal();
		outchar(' ');
		succeed;
	}
	if (seechar('\n')) {
		exitTerminal();
		outchar('\n');
		succeed;
	}
	if (seetext("::=")) {
		exitTerminal();
		outtext("::=");
		succeed;
	}
	if (seechar('|')) {
		exitTerminal();
		outchar('|');
		succeed;
	}
	if (seechar('{')) {
		exitTerminal();
		outchar('{');
		succeed;
	}
	if (seetext("}*")) {
		exitTerminal();
		outtext("}*");
		succeed;
	}
	if (seechar('[')) {
		exitTerminal();
		outchar('[');
		succeed;
	}
	if (seechar(']')) {
		exitTerminal();
		outchar(']');
		succeed;
	}
	fail;
}

enterTerminal() {
	if (inDisplay && inSyntax && !inTerminal) {
		outtext("<userinpuT role=\"terminal\">");
		inTerminal= True;
	}
}

exitTerminal() {
	if (inTerminal) {
		outtext("</userinpuT>");
		inTerminal= False;
	}
}

bool terminal() {
	long bp= bufp;

	if (!inSyntax) fail;
	if (aheadtext("\\<")) fail;
trace("\nterminal:: ");
	seechar('\'');
	enterTerminal();
	other();
	succeed;
}

bool dollar() {
trace("\ndollar:: ");
	if (seetext("$$")) {
		outchar('$');
		succeed;
	}
	fail;
}

bool replaceable() {
	char c;

	if (inSyntax) fail;
trace("\nreplaceable:: ");

	if (seechar('$')) {
		outtext("<replaceable>");

		while ((c= getchar()) != '$' && c != '\n')
			outchar(c);
		outtext("</replaceable>");
		if (c == '\n') outchar(c);
		succeed;
	}
	fail;
}

bool ent() {
	char c;

trace("\nent:: ");
	if (!inProgramOrSyntax) fail;
	if (seetext("\\<")) {
		exitTerminal();
		outchar('<');
		do {
			outchar(c= getchar());
		} while (c != '>' & c!= '\n');
		succeed;
	}
	fail;
}

bool quote() {

	if (inProgramOrSyntax) fail;
trace("\nquote:: ");
	if (!seetext("``")) fail;

	outtext("<quote>");
	inQuote= True;
	succeed;

}

doOutQuote() {
	outtext("</quote>");
	inQuote= False;
}

bool outQuote() {

	if (!inQuote) fail;
trace("\noutQuote:: ");

	if (seetext("''")) {
		doOutQuote();
		succeed;
	}
	if (seetext("</para>")) {
		doOutQuote();
		outtext("</para>");
		succeed;
	}
	if (seetext("<para>")) {
		doOutQuote();
		outtext("<para>");
		succeed;
	}
	fail;
}

bool other() {
trace("\nother:: ");
	if (inProgramOrSyntax && seechar('<')) {
		outtext("&lt;");
		succeed;
	}
	if (inProgramOrSyntax && seechar('>')) {
		outtext("&gt;");
		succeed;
	}
	if (inProgramOrSyntax && seechar('&')) {
		outtext("&amp;");
		succeed;
	}
	outchar(getchar());
	succeed;
}
