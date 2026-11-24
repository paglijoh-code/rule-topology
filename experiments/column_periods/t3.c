/* column_periods/t3.c: full table of the one-push game S1->S2 on [0,N]^3.
   usage: t3 N S1 S2 OUT   writes (N+1)^3 bytes, index (a*M+b)*M+c, T=1 iff P-position.
   Rule: T(x)=1 iff g2(a)^g2(b)^g2(c)!=0 and T(x - s e_i)=0 for all s in S1, all i. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int parse(char *s, int *S){int n=0;char*t;for(t=strtok(s,",");t;t=strtok(0,","))S[n++]=atoi(t);return n;}
int main(int argc,char**argv){int N=atoi(argv[1]),M=N+1,S1[16],S2[16];int n1=parse(argv[2],S1),n2=parse(argv[3],S2);
 int *g=malloc(sizeof(int)*M);for(int h=0;h<=N;h++){unsigned long long seen=0;for(int i=0;i<n2;i++)if(S2[i]<=h)seen|=1ULL<<g[h-S2[i]];int m=0;while(seen>>m&1)m++;g[h]=m;}
 long MM=(long)M*M; uint8_t*T=malloc(MM*M);
 for(int a=0;a<=N;a++)for(int b=0;b<=N;b++)for(int c=0;c<=N;c++){long x=a*MM+(long)b*M+c;int w=(g[a]^g[b]^g[c])==0;
  for(int i=0;i<n1&&!w;i++){int s=S1[i];if((s<=a&&T[x-s*MM])||(s<=b&&T[x-(long)s*M])||(s<=c&&T[x-s]))w=1;}T[x]=!w;}
 FILE*f=fopen(argv[4],"wb");fwrite(T,1,MM*M,f);fclose(f);return 0;}
