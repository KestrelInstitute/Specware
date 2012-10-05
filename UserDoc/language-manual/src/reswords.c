#include <stdio.h>
#include <math.h>
#include <string.h>
#include <ctype.h>

#define MAXS 99
typedef char string[MAXS];

#define MAXRW 999
string reswords[MAXRW];
int rwi;
int sw[MAXRW];
int swi;

int cc[10*MAXRW];
int cci;

int cw[10];
int cwi;

int ceiling(double x) {
	return -floor(-x);
}

main() {
	fillrw();
	printf("[[\n");
	words();
	printf("||\n");
	nonwords();
	printf("]]\n");
}

int mingw, gw;

int h, nc;

words() {
	int wi;

	swi= 0;
	for (wi= 0; wi < rwi; wi++) {
		if (isalpha(*reswords[wi]))
			sw[swi++]= wi;
	}
	mingw= 2;
	for (nc= 9; nc >= 2; nc--) {
		try();
		if (gw == 666) return 0;
	}
}

nonwords() {
	int wi;

	swi= 0;
	for (wi= 0; wi < rwi; wi++) {
		if (*reswords[wi] && !isalpha(*reswords[wi]))
			sw[swi++]= wi;
	}

	mingw= 4;
	for (nc= 9; nc >= 2; nc--) {
		try();
		if (gw == 666) return 0;
	}
}

int max(int a,int b) {
	return a > b ? a : b;
}

try() {
	int c, r, p, mw, tw;

	cci= 0;
	h= (int) ceiling((swi+0.0)/nc);
	nc= (int) ceiling((swi+0.0)/h);
	for (c= 0; c <= nc-1; c++)
		for (r= 0; r <= h-1; r++)
			cc[c + 9*r]= -1;

	for (p= 0; p <= swi-1; p++) {
		c= floor((p+0.0)/h);
		r= p-c*h;
		cc[c + 9*r]= sw[p];
	}

	cwi= tw= 0;
	for (c= 0; c <= nc-1; c++) {
		mw= 0;
		for (r= 0; r <= h-1; r++)
			if (cc[c+9*r] >= 0) mw= max(mw, strlen(reswords[cc[c + 9*r]]));
		cw[c]= mw;
		tw+= mw;
	}

	gw= floor((57.0-tw)/(nc-1));
	if (gw >= mingw) {
		show();
		gw= 666;
	}
}

show() {
	char post_sp, *wp; int c, r, nsp;
char shewn= 0;

	for (r= 0; r <= h-1; r++) {
		printf("||    ");
		nsp= 0;
		for (c= 0; c <= nc-1; c++) {
			while (nsp--) putchar(' ');
			nsp= cw[c]+gw;
			post_sp= 0;
			if (cc[c+9*r] >= 0)
			for (wp= reswords[cc[c + 9*r]]; *wp; wp++)
				if (post_sp || *wp != ' ') {
					putchar(*wp);
					nsp--;
					post_sp= 1;
				}
		}
		putchar('\n');
	}
}

getstr(string s) {
	int p= 0;
	int k;
	while ((k= getchar()) != EOF && k != '\n')
		if (p+1 < MAXS) s[p++]= k;
	s[p]= '\0';
}

#define FINI "FinitaLaStoria!"

fillrw() {
	rwi= 0;
	do {
		if (rwi >= MAXRW) rwi--;
		getstr(reswords[rwi++]);
	} while (strcmp(reswords[rwi-1], FINI) != 0);
	rwi--;
}
