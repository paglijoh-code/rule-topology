/* column_periods/slab.c: the one-push game S1->S2 on three heaps, computed slab by slab in s = a+b+c (the slab CA).
   u_s(a,b) = T(a,b,s-a-b) for a+b <= s. Rule (exactly the game recursion):
     u_s(a,b) = 1  iff  g2(a)^g2(b)^g2(c) != 0  and, for every k in S1, none of
                u_{s-k}(a,b) [if c>=k], u_{s-k}(a-k,b) [if a>=k], u_{s-k}(a,b-k) [if b>=k] is 1.
   usage: slab SMAX S1 S2 OUT [s1 s2 ...]
     writes OUT.st : per slab "s ones" ; OUT.s<S> : slab S as (S+1)^2 bytes, index a*(S+1)+b (2 where a+b>S).
   env FLIP=a,b,c : also run a second copy with T(a,b,c) flipped and write OUT.dmg: per slab "s ndiff" and
       OUT.d<S> slabs of the difference (for listed S).   Memory: ~(KMAX+2) slabs of SMAX^2 bytes. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int parse(char *s, int *S){int n=0;char*t;for(t=strtok(s,",");t;t=strtok(0,","))S[n++]=atoi(t);return n;}
#define R 8
int main(int argc,char**argv){int SM=atoi(argv[1]),S1[16],S2[16];int n1=parse(argv[2],S1),n2=parse(argv[3],S2);char*out=argv[4];
 int ns=argc-5,*want=malloc(sizeof(int)*(ns+1));for(int i=0;i<ns;i++)want[i]=atoi(argv[5+i]);
 int K=0;for(int i=0;i<n1;i++)if(S1[i]>K)K=S1[i]; if(K+1>R){fprintf(stderr,"max S1 too big\n");return 1;}
 int *g=malloc(sizeof(int)*(SM+1));for(int h=0;h<=SM;h++){unsigned long long seen=0;for(int i=0;i<n2;i++)if(S2[i]<=h)seen|=1ULL<<g[h-S2[i]];int m=0;while(seen>>m&1)m++;g[h]=m;}
 long W=SM+1; uint8_t*U[R],*V[R];int fl=0,fa=0,fb=0,fc=0;char*F=getenv("FLIP");if(F){fl=1;sscanf(F,"%d,%d,%d",&fa,&fb,&fc);}
 for(int i=0;i<R;i++){U[i]=calloc(W*W,1);V[i]=fl?calloc(W*W,1):0;}
 char fn[1024];sprintf(fn,"%s.st",out);FILE*fs=fopen(fn,"w");FILE*fd=0;if(fl){sprintf(fn,"%s.dmg",out);fd=fopen(fn,"w");}
 for(int s=0;s<=SM;s++){
  for(int cp=0;cp<1+fl;cp++){uint8_t**X=cp?V:U;uint8_t*Y=X[s%R];long ones=0;
   for(int a=0;a<=s;a++)for(int b=0;a+b<=s;b++){int c=s-a-b;int w=(g[a]^g[b]^g[c])==0;long x=(long)a*W+b;
    for(int i=0;i<n1&&!w;i++){int k=S1[i];if(k>s)continue;uint8_t*Z=X[(s-k)%R];
      if((c>=k&&Z[x])||(a>=k&&Z[x-(long)k*W])||(b>=k&&Z[x-k]))w=1;}
    Y[x]=!w; if(cp&&a==fa&&b==fb&&c==fc)Y[x]=!Y[x]; ones+=Y[x];}
   if(!cp)fprintf(fs,"%d %ld\n",s,ones);}
  if(fl){long d=0;for(int a=0;a<=s;a++)for(int b=0;a+b<=s;b++){long x=(long)a*W+b;d+=U[s%R][x]!=V[s%R][x];}fprintf(fd,"%d %ld\n",s,d);}
  for(int i=0;i<ns;i++)if(want[i]==s){long w2=s+1;uint8_t*o=malloc(w2*w2);
    for(int pass=0;pass<1+fl;pass++){for(int a=0;a<=s;a++)for(int b=0;b<=s;b++)o[a*w2+b]=a+b>s?2:(pass?U[s%R][(long)a*W+b]!=V[s%R][(long)a*W+b]:U[s%R][(long)a*W+b]);
     sprintf(fn,pass?"%s.d%d":"%s.s%d",out,s);FILE*f=fopen(fn,"wb");fwrite(o,1,w2*w2,f);fclose(f);}free(o);}
  /* clear the slot that slab s+1 will overwrite is not needed: every cell a+b<=s+1 is rewritten */
 }
 fclose(fs);if(fd)fclose(fd);return 0;}
