/* rowgen3 N D S1(csv) GPRE(csv or -) GPER(csv) TAILPER OUT [PI PREOUT FROM W0 STEP IDXOUT]
   Rows R_a[d] = P(a,a+d), a<N, d<D, g(x) = gpre[x] for x<|gpre|, else gper[(x-|gpre|)%p].
   Cells d>=D are replaced by the TAILPER-periodic extension of the last TAILPER cells of the row; the last
   4*TAILPER cells must be TAILPER-periodic (else exit 3).
   Plain mode (7 args): OUT = all N rows, N*D bytes.
   Ring mode (13 args): only the last max(S1)+1 rows are kept in memory.  PREOUT (int32 per row) gets
   pre_PI(a) = least y with R_a[x] = R_a[x+PI] for y <= x < D-PI.  OUT gets the rows a with
   a >= FROM or a < W0 or (STEP > 0 and (a % STEP == 0 or a % STEP > STEP - max(S1))), in order;
   IDXOUT (int32) lists their indices. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int c,char**v){
  if(c<8){fprintf(stderr,"usage\n");return 2;}
  long N=atol(v[1]),D=atol(v[2]);int S[64],n=0,P[256],np=0,G[256],p=0,per=atoi(v[6]),mx=0;
  for(char*t=strtok(v[3],",");t;t=strtok(0,","))S[n++]=atoi(t);
  if(strcmp(v[4],"-"))for(char*t=strtok(v[4],",");t;t=strtok(0,","))P[np++]=atoi(t);
  for(char*t=strtok(v[5],",");t;t=strtok(0,","))G[p++]=atoi(t);
  for(int i=0;i<n;i++)if(S[i]>mx)mx=S[i];
  int ring=(c>=14); long RS=ring?mx+1:N;
  int PI=0;long FROM=0,W0=0,STEP=0;FILE*fo=0,*fp=0,*fi=0;
  if(ring){PI=atoi(v[8]);fp=fopen(v[9],"wb");FROM=atol(v[10]);W0=atol(v[11]);STEP=atol(v[12]);
    fo=fopen(v[7],"wb");fi=fopen(v[13],"wb");}
  int*g=malloc(sizeof(int)*(N+D+2));
  for(long x=0;x<N+D+2;x++)g[x]=x<np?P[x]:G[(x-np)%p];
  unsigned char*R=calloc(RS*(long)D,1);
  if(!R){fprintf(stderr,"alloc\n");return 4;}
  #define ROW(a) (R+(((a)%RS))*D)
  for(long a=0;a<N;a++){
    unsigned char*r=ROW(a);
    for(long d=0;d<D;d++){
      int val=(g[a]!=g[a+d]);
      for(int i=0;i<n&&val;i++){int s=S[i];
        if(s<=a){ long dd=d+s; if(dd>=D) dd=D-per+(dd-D)%per; if(ROW(a-s)[dd]) val=0; }
        if(val && s<=a+d){
          if(d>=s){ if(r[d-s]) val=0; }
          else { long a2=a-(s-d); if(a2>=0 && ROW(a2)[s-d]) val=0; }
        }
      }
      r[d]=val;
    }
    for(long d=D-4*per;d<D-per;d++) if(r[d]!=r[d+per]){fprintf(stderr,"row %ld not periodic\n",a);return 3;}
    if(ring){
      int pre=0;
      for(long d=D-PI-1;d>=0;d--) if(r[d]!=r[d+PI]){pre=(int)d+1;break;}
      fwrite(&pre,4,1,fp);
      if(a>=FROM||a<W0||(STEP>0&&(a%STEP==0||a%STEP>STEP-mx))){fwrite(r,1,D,fo);int ia=(int)a;fwrite(&ia,4,1,fi);}
    }
  }
  if(!ring){FILE*f=fopen(v[7],"wb");fwrite(R,1,N*(long)D,f);fclose(f);}
  else{fclose(fo);fclose(fp);fclose(fi);}
  return 0;}
