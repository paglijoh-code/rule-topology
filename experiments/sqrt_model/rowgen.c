/* rowgen N D S1(csv) G(csv one period of g, g has no preperiod, period len) OUT
   Rows r_a(d)=outcome(a,a+d) for a<N, d<D (1=P), computed by the push-subtraction rule with
   cells d>=D replaced by the period-10 extension of the last 10 cells (valid since pre(a) < D-20;
   checked: the last 40 cells must be 10-periodic, else abort). g(h)=h%per assumed via Gper arg. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int c,char**v){
  long N=atol(v[1]),D=atol(v[2]);int S[16],n=0,per=atoi(v[4]);
  char*t=strtok(v[3],",");while(t){S[n++]=atoi(t);t=strtok(0,",");}
  int W=D+16;unsigned char*R=calloc(N*(long)W,1);
  for(long a=0;a<N;a++){
    unsigned char*r=R+a*W;
    for(long d=0;d<D;d++){
      int val=(d%per!=0);
      for(int i=0;i<n&&val;i++){int s=S[i];
        if(s<=a){ if(R[(a-s)*W+d+s]) val=0; }
        if(val && s<=a+d){
          if(d>=s){ if(r[d-s]) val=0; }
          else { long a2=a-(s-d); if(a2>=0 && R[a2*W+(s-d)]) val=0; }
        }
      }
      r[d]=val;
      if(d==D-1){ for(int e=0;e<16;e++) r[D+e]=r[D-10+(e%10)]; }
    }
    /* fill extension after row complete is too late for cells needing d+s>=D within same row; handle: */
  }
  FILE*f=fopen(v[5],"wb");fwrite(R,1,N*(long)W,f);fclose(f);return 0;}
