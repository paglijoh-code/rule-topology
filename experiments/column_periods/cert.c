/* column_periods/cert.c: computer-assisted certificate of exact eventual column periods on the box Q = [0,A]^2 x [0,C].
   Facts used: (i) Q is closed under moves, so T on Q is exact;
   (ii) for c >= KMAX, the plane T(.,.,c+1)|[0,A]^2 is a function of the planes c-KMAX+1..c and of c mod per(g2);
   hence if T(a,b,c+P) = T(a,b,c) for every (a,b) and every c in [h, h+KMAX-1], with per(g2) | P, then every column
   of Q is P-periodic from height h on (induction on c).
   The program checks T(c+P)=T(c) for all columns and all c in [h, C-P] with h = C-P-L (L >= KMAX-1),
   then, for each column, its least period d | P on the window [h, h+P-1] (exact minimal period of the tail).
   usage: cert A C S1 S2 P L   prints "CERT ok" or "CERT fail a b c", then per-period counts and, for each period,
   the minimal a+b and the column attaining it; writes per-column "a b d" to stdout after "COLUMNS" if env COLS=1. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int parse(char *s, int *S){int n=0;char*t;for(t=strtok(s,",");t;t=strtok(0,","))S[n++]=atoi(t);return n;}
int main(int argc,char**argv){char s1n[64],s2n[64];snprintf(s1n,64,"%s",argv[3]);snprintf(s2n,64,"%s",argv[4]);int A=atoi(argv[1]),C=atoi(argv[2]),S1[16],S2[16];int n1=parse(argv[3],S1),n2=parse(argv[4],S2);int P=atoi(argv[5]),L=atoi(argv[6]);
 int K=0;for(int i=0;i<n1;i++)if(S1[i]>K)K=S1[i];int R=K+1;int h=C-P-L;
 int H=C+1;int*g=malloc(sizeof(int)*(H+A+2));for(int x=0;x<H+A+2;x++){unsigned long long seen=0;for(int i=0;i<n2;i++)if(S2[i]<=x)seen|=1ULL<<g[x-S2[i]];int m=0;while(seen>>m&1)m++;g[x]=m;}
 int pg=0;for(int p=1;p<100&&!pg;p++){int ok=1;for(int x=0;x<H;x++)if(x+p<H+A+2&&g[x]!=g[x+p]){ok=0;break;}if(ok)pg=p;}
 if(!pg||P%pg||L<K-1||h<K){printf("CERT bad parameters (per g2 = %d)\n",pg);return 1;}
 long MA=A+1;uint8_t*T=malloc((long)R*MA*H);long cnt[4096]={0};int mins[4096],ma[4096],mb[4096];for(int i=0;i<4096;i++)mins[i]=1<<30;
 int cols=getenv("COLS")!=0;
 #define COL(a,b) (T+((long)((a)%R)*MA+(b))*H)
 for(int a=0;a<=A;a++){for(int b=0;b<=A;b++){uint8_t*col=COL(a,b);
   for(int c=0;c<=C;c++){int w=(g[a]^g[b]^g[c])==0;
    for(int i=0;i<n1&&!w;i++){int s=S1[i];if((s<=a&&COL(a-s,b)[c])||(s<=b&&COL(a,b-s)[c])||(s<=c&&col[c-s]))w=1;}
    col[c]=!w;}
   for(int c=h;c<=C-P;c++)if(col[c]!=col[c+P]){printf("CERT fail %d %d %d\n",a,b,c);return 2;}
   int d=0;for(int q=1;q<=P&&!d;q++){if(P%q)continue;int ok=1;for(int c=h;c<h+P;c++)if(col[c]!=col[c+q]){ok=0;break;}if(ok)d=q;}
   cnt[d]++;if(a+b<mins[d]){mins[d]=a+b;ma[d]=a;mb[d]=b;}
   if(cols)printf("%d %d %d\n",a,b,d);}}
 printf("CERT ok: A=%d C=%d S1=%s S2=%s P=%d: every column of [0,%d]^2 is %d-periodic in c from height %d (per g2 = %d)\n",A,C,s1n,s2n,P,A,P,h,pg);
 for(int d=1;d<=P;d++)if(cnt[d])printf("period %d: %ld columns, first at a+b=%d (a,b)=(%d,%d)\n",d,cnt[d],mins[d],ma[d],mb[d]);
 return 0;}
