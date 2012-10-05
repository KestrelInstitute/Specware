#include <stdio.h>
#include <string.h>

typedef char bool;
#define true  1
#define false 0

typedef char *string;

string ignore[10]= {
	"Preliminaries",
	"The grammar description formalism",
	"Projectors",
	"Relaxators",
	"Restrictors",
	"Quotienters",
	"Choosers",
	"Embedders",
	"Embedding-tests",
	"Selectors"
};

#define MAXS 999
typedef char sstring[MAXS];
sstring line, fp; string formalpara;
bool in_formalpara, serious;

main() {
	formalpara= fp; formalpara[0]= '\0'; in_formalpara= false;
	serious= false;
	getstr(line);
	while(strcmp(line, "ZeEnd") != 0) {
		process();
		getstr(line);
	}
	close();
}

sstring title; string post_title;

process() {
	if (strncmp(line, "<section", (size_t) 8) == 0) {
		get_title();
		if (tstatus()) {
			strcpy(fp, line); formalpara= fp;
			while(*formalpara && *formalpara != '>')
				formalpara++;
			// formalpara|1= "<formalpara>";
			formalpara++;
			serious= true;
		}
	} else if (strcmp(line, "<<") == 0)
		rules();
}

get_title() {
	int p;
	for (p= 0; p+7 < strlen(line); p++)
	if (strncmp(line+p, "<title>", (size_t) 7) == 0) {
		post_title= line+(p+7);
		for (p= 0; p+1 < strlen(post_title); p++)
		if (post_title[p] == '<') {
			strncpy(title, post_title, (size_t) p);
			title[p]= '\0';
		}
		return;
	}
}

int tstatus() {
	int i;
	for (i= 0; i < 10; i++)
	if (strcmp(title, ignore[i]) == 0) return false;
	return true;
}

rules() {
	if (!serious) return;
	if (*formalpara) {
		close();
		printf("<formalpara>%s\n", formalpara);
		printf("<para>\n");
		formalpara= fp; formalpara[0]= '\0'; in_formalpara= true;
	}
	while(strcmp(line, ">>") != 0) {
		if (strncmp(line, "||", (size_t) 2) == 0 && strncmp(line, "|| ", (size_t) 3) != 0)
			printf("||  %s\n", line+2);
		else
			printf("%s\n", line);
		getstr(line);
	}
	printf("%s\n", line);
}

close() {
	if (!in_formalpara) return;
	printf("</para>\n");
	printf("</formalpara>\n");
	printf("<!-- ***************************************************************** -->\n");
	in_formalpara= false;
}

getstr(string s) {
	int p= 0;
	int k;
	while ((k= getchar()) != EOF && k != '\n')
		if (p+1 < MAXS) s[p++]= k;
	s[p]= '\0';
}
