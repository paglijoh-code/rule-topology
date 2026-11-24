/* column_periods/colbox.c: table on the box [0,A]x[0,A]x[0,C] (closed under moves, so exact), then for every column (a,b)
   the least eventual period p <= PMAX (checked on the top window: T(c)=T(c+p) for all c in [C-p-WIN, C-p]) and its
   preperiod (1 + last c <= C-p with T(c) != T(c+p)).  usage: colbox A C S1 S2 PMAX WIN > out   lines "a b p pre" (p=0: none found) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int parse(char *s, int *S){int n=0;char*t;for(t=strtok(s,",");t;t=strtok(0,","))S[n++]=atoi(t);return n;}
int main(int argc,char**argv){int A=atoi(argv[1]),C=atoi(argv[2]),S1[16],S2[16];int n1=parse(argv[3],S1),n2=parse(argv[4],S2);int PM=atoi(argv[5]),WIN=atoi(argv[6]);
 int H=C+1;int*g=malloc(sizeof(int)*(H+A+2));for(int h=0;h<H+A+2;h++){unsigned long long seen=0;for(int i=0;i<n2;i++)if(S2[i]<=h)seen|=1ULL<<g[h-S2[i]];int m=0;while(seen>>m&1)m++;g[h]=m;}
 long MA=A+1;uint8_t*T=malloc(MA*MA*H);
 for(int a=0;a<=A;a++)for(int b=0;b<=A;b++){uint8_t*col=T+((long)a*MA+b)*H;
  for(int c=0;c<=C;c++){int w=(g[a]^g[b]^g[c])==0;
   for(int i=0;i<n1&&!w;i++){int s=S1[i];if((s<=a&&T[((long)(a-s)*MA+b)*H+c])||(s<=b&&T[((long)a*MA+b-s)*H+c])||(s<=c&&col[c-s]))w=1;}
   col[c]=!w;}}
 for(int a=0;a<=A;a++)for(int b=0;b<=A;b++){uint8_t*col=T+((long)a*MA+b)*H;int P=0,pre=-1;
  for(int p=1;p<=PM&&!P;p++){int ok=1;for(int c=C-p-WIN;c<=C-p;c++)if(col[c]!=col[c+p]){ok=0;break;}
   if(ok){P=p;int c=C-p;while(c>=0&&col[c]==col[c+p])c--;pre=c+1;}}
  printf("%d %d %d %d\n",a,b,P,pre);}
 if(getenv("DUMP")){FILE*f=fopen(getenv("DUMP"),"wb");fwrite(T,1,MA*MA*H,f);fclose(f);}
 return 0;}
