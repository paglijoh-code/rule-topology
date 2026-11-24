/* column_periods/damage.c: damage spreading. usage: damage N S1 S2 a0 b0 c0 [mode]
   Computes T and T' where T' has the cell x0 flipped (mode 0) or the P2 forcing at x0 flipped (mode 1),
   then prints, for each d = max_i(x_i - x0_i), the number of cells in the shell with T != T' and the shell size.
   env DUMPW=w0 DUMPF=file: write the 64^3 windows of T then U with corner (w0,w0,w0).
   Only the upper octant x >= x0 can differ. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int parse(char *s, int *S){int n=0;char*t;for(t=strtok(s,",");t;t=strtok(0,","))S[n++]=atoi(t);return n;}
int main(int argc,char**argv){int N=atoi(argv[1]),M=N+1,S1[16],S2[16];int n1=parse(argv[2],S1),n2=parse(argv[3],S2);
 int A0=atoi(argv[4]),B0=atoi(argv[5]),C0=atoi(argv[6]),mode=argc>7?atoi(argv[7]):0;
 int *g=malloc(sizeof(int)*M);for(int h=0;h<=N;h++){unsigned long long seen=0;for(int i=0;i<n2;i++)if(S2[i]<=h)seen|=1ULL<<g[h-S2[i]];int m=0;while(seen>>m&1)m++;g[h]=m;}
 long MM=(long)M*M; uint8_t*T=malloc(MM*M),*U=malloc(MM*M);
 long *dam=calloc(M,8),*sz=calloc(M,8);
 for(int a=0;a<=N;a++)for(int b=0;b<=N;b++)for(int c=0;c<=N;c++){long x=a*MM+(long)b*M+c;int p2=(g[a]^g[b]^g[c])==0;
  int w=p2,w2=p2; int at=(a==A0&&b==B0&&c==C0); if(at&&mode==1)w2=!w2;
  for(int i=0;i<n1&&!w;i++){int s=S1[i];if((s<=a&&T[x-s*MM])||(s<=b&&T[x-(long)s*M])||(s<=c&&T[x-s]))w=1;}
  for(int i=0;i<n1&&!w2;i++){int s=S1[i];if((s<=a&&U[x-s*MM])||(s<=b&&U[x-(long)s*M])||(s<=c&&U[x-s]))w2=1;}
  T[x]=!w;U[x]=!w2; if(at&&mode==0)U[x]=!U[x];
  if(a>=A0&&b>=B0&&c>=C0){int d=a-A0;if(b-B0>d)d=b-B0;if(c-C0>d)d=c-C0;sz[d]++;dam[d]+=T[x]!=U[x];}}
 if(getenv("DUMPW")){int w0=atoi(getenv("DUMPW")),L=64;FILE*f=fopen(getenv("DUMPF"),"wb");for(int a=w0;a<w0+L;a++)for(int b=w0;b<w0+L;b++)fwrite(T+a*MM+(long)b*M+w0,1,L,f);for(int a=w0;a<w0+L;a++)for(int b=w0;b<w0+L;b++)fwrite(U+a*MM+(long)b*M+w0,1,L,f);fclose(f);}
 for(int d=0;d<=N;d++)if(sz[d]&&d+A0<=N&&d+B0<=N&&d+C0<=N)printf("%d %ld %ld\n",d,dam[d],sz[d]);return 0;}
