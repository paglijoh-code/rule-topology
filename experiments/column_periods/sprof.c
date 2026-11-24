/* column_periods/sprof.c: local order map of one slab file (from slab.c). For patch centres on a grid of step G,
   P x P patch, minimal mismatch over in-slab shifts (i,j) (3D shift (i,j,-i-j)), 0<max(|i|,|j|)<=R.
   usage: sprof SLABFILE S P R G   prints "a b c dmirror minmis i j density" for patches fully inside the slab
   (dmirror = min(|a-b|,|b-c|,|a-c|) at the patch centre). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc,char**argv){int S=atoi(argv[2]),P=atoi(argv[3]),R=atoi(argv[4]),G=atoi(argv[5]);long W=S+1;
 uint8_t*X=malloc(W*W);FILE*f=fopen(argv[1],"rb");if(fread(X,1,W*W,f)!=(size_t)(W*W))return 1;fclose(f);
 for(int a0=R;a0+P+R<=S;a0+=G)for(int b0=R;a0+b0+P+P+2*R<=S;b0+=G){
  int best=P*P+1,bi=0,bj=0,ones=0;for(int x=0;x<P;x++)for(int y=0;y<P;y++)ones+=X[(a0+x)*W+b0+y];
  for(int i=-R;i<=R;i++)for(int j=-R;j<=R;j++){if(!i&&!j)continue;int m=0;
   for(int x=0;x<P&&m<best;x++){uint8_t*p=X+(a0+x)*W+b0,*q=X+(a0+x+i)*W+b0+j;for(int y=0;y<P;y++)m+=p[y]!=q[y];}
   if(m<best){best=m;bi=i;bj=j;}}
  int a=a0+P/2,b=b0+P/2,c=S-a-b;int d1=abs(a-b),d2=abs(b-c),d3=abs(a-c);int dm=d1<d2?d1:d2;if(d3<dm)dm=d3;
  printf("%d %d %d %d %.4f %d %d %.4f\n",a,b,c,dm,(double)best/(P*P),bi,bj,(double)ones/(P*P));}
 return 0;}
