/* column_periods/torus.c: the slab CA of S1->S2 on an L x L torus (L a multiple of the Grundy period of S2), from a random start.
   u_s(a,b) = 1 iff P2(a,b,s-a-b) fails and, for k in S1, u_{s-k}(a,b), u_{s-k}(a-k,b), u_{s-k}(a,b-k) are all 0 (indices mod L).
   This is the interior rule of the real table with the boundary (faces) removed.
   usage: torus L S1 S2 seed SMAX   prints transient and period of the state (last KMAX slabs, at s = 0 mod per(g2)),
   or "none" if no repeat by SMAX; also prints density of the last slab and, with env DMG=1, damage spreading
   (one flipped cell at s=100) as fraction of differing cells at s = 100+100k. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int parse(char *s, int *S){int n=0;char*t;for(t=strtok(s,",");t;t=strtok(0,","))S[n++]=atoi(t);return n;}
static uint64_t hs(uint8_t*p,long n,uint64_t h){for(long i=0;i<n;i++){h^=p[i]+0x9e3779b97f4a7c15ULL+(h<<6)+(h>>2);}return h;}
int main(int argc,char**argv){int L=atoi(argv[1]),S1[16],S2[16];int n1=parse(argv[2],S1),n2=parse(argv[3],S2);unsigned seed=atoi(argv[4]);long SM=atol(argv[5]);
 int K=0;for(int i=0;i<n1;i++)if(S1[i]>K)K=S1[i];
 int g[4096];for(int h=0;h<4096;h++){unsigned long long seen=0;for(int i=0;i<n2;i++)if(S2[i]<=h)seen|=1ULL<<g[h-S2[i]];int m=0;while(seen>>m&1)m++;g[h]=m;}
 int per=1;for(int p=1;p<200;p++){int ok=1;for(int h=300;h<1000;h++)if(g[h]!=g[h+p]){ok=0;break;}if(ok){per=p;break;}}
 if(L%per){fprintf(stderr,"L must be a multiple of %d\n",per);return 1;}
 int dm=getenv("DMG")!=0; int R=K+1; long LL=(long)L*L;
 uint8_t*U=calloc(R*LL,1),*V=calloc(R*LL,1); srand(seed);
 for(int s=0;s<K;s++)for(long x=0;x<LL;x++)U[s*LL+x]=V[s*LL+x]=(rand()%7)==0;
 long cap=1<<22;uint64_t*HK=calloc(cap,8);long*HT=calloc(cap,8);int found=0;
 for(long s=K;s<=SM;s++){
  for(int cp=0;cp<1+dm;cp++){uint8_t*X=cp?V:U;uint8_t*Y=X+(s%R)*LL;
  for(int a=0;a<L;a++)for(int b=0;b<L;b++){int c=(int)(((s-a-b)%L+L)%L);int w=(g[a%per]^g[b%per]^g[c%per])==0;
   for(int i=0;i<n1&&!w;i++){int k=S1[i];uint8_t*Z=X+((s-k)%R)*LL;if(Z[a*L+b]||Z[((a-k+L)%L)*L+b]||Z[a*L+(b-k+L)%L])w=1;}
   Y[a*L+b]=!w;}
  if(cp&&s==100)Y[(L/2)*L+L/3]^=1;}
  if(dm&&s>100&&(s-100)%100==0){long d=0;for(long x=0;x<LL;x++)d+=U[(s%R)*LL+x]!=V[(s%R)*LL+x];printf("dmg s=%ld %.4f\n",s,(double)d/LL);}
  if(!found&&s%per==0&&!dm){uint64_t h=1469598103934665603ULL;for(int j=0;j<K;j++)h=hs(U+((s-j)%R)*LL,LL,h);
   long i=h&(cap-1);while(HK[i]&&HK[i]!=h)i=(i+1)&(cap-1);
   if(HK[i]==h){printf("L=%d seed=%u transient<=%ld period=%ld\n",L,seed,HT[i],s-HT[i]);found=1;break;}
   HK[i]=h;HT[i]=s;}
 }
 long ones=0;for(long x=0;x<LL;x++)ones+=U[(SM%R)*LL+x];
 if(!found&&!dm)printf("L=%d seed=%u none by %ld\n",L,seed,SM);
 return 0;}
