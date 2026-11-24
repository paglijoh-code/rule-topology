/* column_periods/colring.c: like colbox.c but keeps only a ring of KMAX+1 a-rows (memory ~ 5 (A+1) (C+1) bytes), so large A works.
   The box [0,A]x[0,A]x[0,C] is closed under moves, so every value is exact.
   For each column (a,b): least eventual period p <= PMAX verified on [C-p-WIN, C] and its preperiod.
   usage: colring A C S1 S2 PMAX WIN > out   lines "a b p pre" (p=0: no period <= PMAX visible).
   env WORDS=file: also write, for each column with p>0, the 64-bit hash of its period word aligned at c = C-p-WIN..  (unused if unset) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int parse(char *s, int *S){int n=0;char*t;for(t=strtok(s,",");t;t=strtok(0,","))S[n++]=atoi(t);return n;}
int main(int argc,char**argv){int A=atoi(argv[1]),C=atoi(argv[2]),S1[16],S2[16];int n1=parse(argv[3],S1),n2=parse(argv[4],S2);int PM=atoi(argv[5]),WIN=atoi(argv[6]);
 int K=0;for(int i=0;i<n1;i++)if(S1[i]>K)K=S1[i];int R=K+1;
 int H=C+1;int*g=malloc(sizeof(int)*(H+A+2));for(int h=0;h<H+A+2;h++){unsigned long long seen=0;for(int i=0;i<n2;i++)if(S2[i]<=h)seen|=1ULL<<g[h-S2[i]];int m=0;while(seen>>m&1)m++;g[h]=m;}
 long MA=A+1;uint8_t*T=malloc((long)R*MA*H);
 #define COL(a,b) (T+((long)((a)%R)*MA+(b))*H)
 for(int a=0;a<=A;a++){for(int b=0;b<=A;b++){uint8_t*col=COL(a,b);
   for(int c=0;c<=C;c++){int w=(g[a]^g[b]^g[c])==0;
    for(int i=0;i<n1&&!w;i++){int s=S1[i];if((s<=a&&COL(a-s,b)[c])||(s<=b&&COL(a,b-s)[c])||(s<=c&&col[c-s]))w=1;}
    col[c]=!w;}}
  for(int b=0;b<=A;b++){uint8_t*col=COL(a,b);int P=0,pre=-1;
   for(int p=1;p<=PM&&!P;p++){int ok=1;for(int c=C-p-WIN;c<=C-p;c++)if(col[c]!=col[c+p]){ok=0;break;}
    if(ok){P=p;int c=C-p;while(c>=0&&col[c]==col[c+p])c--;pre=c+1;}}
   printf("%d %d %d %d\n",a,b,P,pre);}
  fflush(stdout);}
 return 0;}
