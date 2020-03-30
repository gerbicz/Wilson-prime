// Written by Robert Gerbicz
// Fast algorithm for p<2^61.

// A totally brute force code:
// F(p)=r=Mod(1,p*p);for(i=1,p-1,r*=i);return(lift(r))

// some lines: (verified by slow wilsonremainder() function)
// p      (p-1)! mod p*p
// 999979 496398575410
// 999983 285106153112
// 9999973 43866321560611
// 9999991 10433100610200
// 100000007 2797130195799099
// 1000000007 248930608742514248 ( 57 sec. )
// 10000000019 1104594712098729948 ( 634 sec. )
// 10000000033 43243222192702632764
// 10000000061 23299102792124526164
// 10000000069 69886760102218641377
// 10000000097 50793644052698342531
// 10000000103 11469982338140816865
// 10000000121 65303769910175606351
// 10000000141 31024748547448948350
// 10000000147 57730848208643456191
// 10000000207 61378175160528199522
// 10000000259 32074431130727744769
// 10000000277 42942022099493979206
// 10000000279 43120855923071846687
// 10000000319 17819587048444808711
// 10000000343 76154581452102054211
// 10000000391 99209804339103197985
// 10000000403 25979094576957469258
// 10000000469 879234071236076006
// 10000000501 60803870386273753733
// 10000000537 19695429747644520652

// some other useful data: (here 1k=1000,1M=10^6,1B=10^9,1T=10^12)
// primepi(25k)=2762
// primepi(50k)=5133
// primepi(100k)=9592
// primepi(1M)=78498
// primepi(10M)=664579
// primepi(25M)=1565927
// primepi(50M)=3001334
// primepi(500M)=26355867

// on 64 bits, one core, 2.1 GHz AMD Phenom with 2 GB RAM, gmp-5.0.1
// st   en   interval maxmemory usage  time
// 0    50M  2M       44MB RAM ?       671 sec.
// 0    10B  10M      841MB RAM ??     approx. 420000 sec.

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>// for sqrt
#include <assert.h>
#include "gmp.h"

#define bound 100
// print out all solutions, where (p-1)! == -1+k*p mod p^2 for abs(k)<=bound
#define BR 128
// process approx. interval/BR primes at once in a smaller group
#define reps 10

typedef long long int lli;

void wilsonremainder(mpz_ptr,mpz_t);
lli wilson21(lli);
void longlongtompz(mpz_ptr,lli);
lli mpztolonglong(mpz_t);
void producttree(mpz_ptr,mpz_t*,lli,lli);
void producttree2(mpz_ptr,lli,lli);
void remaindertree(mpz_t,mpz_t *,mpz_t *,lli,lli);
void remaindertree2(mpz_t,mpz_t *,mpz_t *,lli,lli);
void func(lli,lli,mpz_t *,mpz_t *,lli *,int,lli,lli,int);
lli factorialp(lli,lli);
lli factorialp2(lli,lli,lli);
void initprimes(int);
void mpzredsquare(mpz_t,mpz_t,mpz_t);
void mpzredspec(mpz_t,mpz_t);
void mpzred(mpz_t,mpz_t,mpz_t,mpz_t);
void ff(mpz_ptr,mpz_t,lli);
void ff2(mpz_ptr,mpz_t,lli,lli,lli);

lli interval;
int sievelen,primepi,*prime;

void wilsonremainder(mpz_ptr res,mpz_t p){
// slow, no big tricks, not used, no limitation for p
// just for educational purpose
// Computation of res=(p-1)! mod p*p
    int ext=0;
    mpz_t i,p2;
    mpz_init_set_ui(i,2);
    mpz_init(p2);
    mpz_pow_ui(p2,p,2);
    mpz_set_ui(res,1);
    
    while(mpz_cmp(i,p)<0)  {
        ext++;
        mpz_mul(res,res,i);
        mpz_add_ui(i,i,1);
        if(ext==6){mpz_mod(res,res,p2);ext=0;}// reduce after every six multiplication, before reduction 0<res<p^8
    }
    mpz_mod(res,res,p2);
    
    mpz_clear(i);
    mpz_clear(p2);
    return;
}

lli wilson21(lli p)  {// slow, not used, p<2^21
   assert(p>0&&p<(1<<21));
   lli res=1,i,p2=p*p;
   for(i=2;i<p;i++)res=(res*i)%p2;// 0<res<p^3<2^63, so fits in long long int type
   return res;
}

// conversion from 62 bits long long to mpz type
void longlongtompz(mpz_ptr x,lli n)  {
    int hi,lo;
    
    lo=n&0x7fffffff;
    n>>=31;
    hi=n;
    
    mpz_set_ui(x,hi);
    mpz_mul_2exp(x,x,31);
    mpz_add_ui(x,x,lo);
    return;
}
// the other direction
lli mpztolonglong(mpz_t x)  {
    
    mpz_t temp;
    mpz_init(temp);
    lli ret;
    
    mpz_fdiv_q_2exp(temp,x,31);
    ret=mpz_get_ui(temp);
    ret<<=31;
    mpz_fdiv_r_2exp(temp,x,31);
    ret+=mpz_get_ui(temp);
    mpz_clear(temp);
    
    return ret;
}

void producttree (mpz_ptr result,mpz_t* vec,lli pos1,lli pos2)  {
// Mulptiplication by binary splitting with product tree.
// result=prod(i=pos1,pos2,vec[i])
  if(pos1>pos2) {
     mpz_set_ui(result,1);// empty product is one.
     return;
  }
  
  if(pos1==pos2)  {
     mpz_set (result,vec[pos1]);
     return;
  }
  
  if(pos2<=pos1+2)  {
     lli i;
     mpz_set(result,vec[pos1]);
     for(i=pos1+1;i<=pos2;i++)
         mpz_mul(result,result,vec[i]);
     return;
  }

  lli mid=(pos1+pos2)>>1;
  mpz_t temp;
  
  producttree(result,vec,pos1,mid);
  mpz_init(temp);
  
  producttree(temp,vec,mid+1,pos2);
  mpz_mul(result,result,temp);
  
  mpz_clear(temp);
  return;
}

void producttree2 (mpz_ptr result,lli pos1,lli pos2)  {
// Mulptiplication by binary splitting with product tree.
// result=prod(i=pos1,pos2,i)
  if(pos1>pos2)  {
     mpz_set_ui(result,1);// empty product is one.
     return;
  }
  
  if(pos1==pos2)  {
     longlongtompz(result,pos1);
     return;
  }
  
  lli mid=(pos1+pos2)/2;
  mpz_t temp;
  
  producttree2(result,pos1,mid);
  mpz_init(temp);
  
  producttree2(temp,mid+1,pos2);
  mpz_mul(result,result,temp);
  
  mpz_clear(temp);
  return;
}

void remaindertree(mpz_t v,mpz_t *vec,mpz_t *res,lli pos1,lli pos2)  {
// Computation of res[i]=(res[i]*v)%(vec[i]*vec[i]) for pos1<=i<=pos2 with remainder tree.
// memory efficient version, rebuild the (partial) product tree at each level
    if(pos1>pos2||mpz_cmp_ui(v,1)==0)  return;
    
    mpz_t temp;
    mpz_init(temp);
    if(pos1==pos2)  {
       mpz_t p2;
       mpz_init(p2);
       mpz_pow_ui(p2,vec[pos1],2);
       mpz_mul(temp,res[pos1],v);
       mpz_mod(res[pos1],temp,p2);
       mpz_clear(temp);
       mpz_clear(p2);
       return;
    }
    lli mid=(pos1+pos2)>>1;
    
    producttree(temp,vec,pos1,mid);
    mpzredspec(v,temp);
    remaindertree(temp,vec,res,pos1,mid);
    
    producttree(temp,vec,mid+1,pos2);
    mpzredspec(v,temp);
    remaindertree(temp,vec,res,mid+1,pos2);
    
    mpz_clear(temp);
    return;
}

void remaindertree2(mpz_t v,mpz_t *vec,mpz_t *res,lli pos1,lli pos2)  {
// Computation of res[i]=(res[i]*v)%(vec[i]*vec[i]) for pos1<=i<=pos2 with remainder tree.
// memory costly version
   lli i,L=pos2-pos1+1;
   mpz_t *T,temp,p2;
   T=(mpz_t*)(malloc)((2*L)*sizeof(mpz_t));
   for(i=0;i<2*L;i++)mpz_init(T[i]);
   mpz_init(temp);
   mpz_init(p2);

   for(i=0;i<L;i++)mpz_set(T[L+i],vec[i+pos1]);
       
   // product tree
   for(i=L-1;i>0;i--)mpz_mul(T[i],T[2*i],T[2*i+1]);
       
   //remainder tree
   mpz_pow_ui(T[1],T[1],2);
   mpz_mod(T[1],v,T[1]);
   for(i=2;i<2*L;i++)  {
       mpz_pow_ui(T[i],T[i],2);
       mpz_mod(T[i],T[i>>1],T[i]);
       if(i&1)  mpz_clear(T[i>>1]);
   }
       
   for(i=pos1;i<=pos2;i++)  {
       mpz_mul(temp,res[i],T[L+i-pos1]);
       mpz_pow_ui(p2,vec[i],2);
       mpz_mod(res[i],temp,p2);
   }
       
   for(i=L;i<2*L;i++)mpz_clear(T[i]);
   mpz_clear(T[0]);
   free(T);
   mpz_clear(temp);
   mpz_clear(p2);
   return;
}

void func(lli n1,lli n2,mpz_t *vec,mpz_t *res,lli *firstp,int d,lli pos1,lli pos2,int offset)  {
// compute n1*(n1+1)*...*u mod vec[i]^2 for all pos1<=i<=pos2, where u=min(n2-1,(firstp[i]-1)/d)
// (update the res table)
// warning: n2 is not included in the product
// 0<=offset<8, so eight different strategy for func
    if(n1>=n2||pos1>pos2)  return;
    
    int ext=0;
    lli i,stpos1=pos1,pos,pos3,pow2,N;

    if(offset&1)  N=n2;
    else  {
       N=n1+interval;
       if(N>n2) N=n2;
    }

    if(n2-n1==1)  {
       mpz_t temp,p2,gmpn1;
       mpz_init(temp);
       mpz_init(p2);
       mpz_init(gmpn1);
       longlongtompz(gmpn1,n1);
       for(i=pos1;i<=pos2;i++){
       // check if n1<=(firstp[i]-1)/d
       if(n1<=(firstp[i]-1)/d)  {
          mpz_mul(temp,res[i],gmpn1);
          mpz_pow_ui(p2,vec[i],2);
          mpz_mod(res[i],temp,p2);
       }}
       mpz_clear(temp);
       mpz_clear(p2);
       mpz_clear(gmpn1);
       return;
    }
    else  {
    // check N>(firstp[pos1]-1)/d
    mpz_t T,temp;
    mpz_init(T);
    mpz_init(temp);

    if(N>(firstp[pos1]-1)/d)  {
       N=(N+n1)/2;
       pos3=0;
       pow2=1;while(pow2<=pos2/2)pow2<<=1;
       // binary search
       while(pow2){
             pos=pos3+pow2;
             if(pos<=pos2&&(firstp[pos]-1)/d+1<=N)pos3=pos;
             pow2>>=1;
       }
       func(n1,N,vec,res,firstp,d,pos1,pos3,offset);
       func(N,n2,vec,res,firstp,d,pos3+1,pos2,offset);
       pos1=pos3+1;
       ext=1;// the rest of it done here
    }
    
    if(n1<N&&pos1<=pos2)  {

    if((offset>>1)&1)  {
        producttree2(T,n1,N-1);
        if(offset>>2)  remaindertree2(T,vec,res,pos1,pos2);
        else           remaindertree(T,vec,res,pos1,pos2);
    }
    else  {
        producttree(temp,vec,pos1,pos2);
        ff2(T,temp,pos2-pos1+1,n1-1,N-1);
        if(offset>>2)  remaindertree2(T,vec,res,pos1,pos2);
        else           remaindertree(T,vec,res,pos1,pos2);
    }}
    mpz_clear(T);
    mpz_clear(temp);
    }
        
    if(ext==0)  func(N,n2,vec,res,firstp,d,stpos1,pos2,offset);
    return;
}

lli factorialp(lli n,lli p)  {
// p^ret is the exact p divisor of n!
    if(n<p)return 0;
    lli ret=0;
    while(n)  {
          n/=p;
          ret+=n;
    }
    return ret;
}

lli factorialp2(lli n,lli p,lli b)  {
//  p^ret is the exact p divisor of n!, excluding p^e factors where p^e>b
    if(n<p)return 0;
    lli ret=0,q=1,lim=b/p;
    
    while(q<=lim){
          n/=p;
          ret+=n;
          q*=p;
    }
    return ret;
}
    
void initprimes(int n)  {

    unsigned int *isprime,Bits[32];
    int i,j,si=n/32+1;
    isprime=(unsigned int*)(malloc)(si*sizeof(unsigned int));
    for(i=0;i<si;i++)  isprime[i]=0xffffffff;
    Bits[0]=1;
    for(i=1;i<32;i++)Bits[i]=2*Bits[i-1];
    
    isprime[0]&=~Bits[0];
    isprime[0]&=~Bits[1];
    for(i=0;i*i<n;i++)
        if((isprime[i>>5]&Bits[i&31])>0)  {
           for(j=i*i;j<n;j+=i)  isprime[j>>5]&=~Bits[j&31];
        }
    
    primepi=0;
    for(i=0;i<n;i++)
        if((isprime[i>>5]&Bits[i&31])>0)  primepi++;
    prime=(int*)(malloc)(primepi*sizeof(int));
    primepi=0;
    for(i=0;i<n;i++)
        if((isprime[i>>5]&Bits[i&31])>0)  prime[primepi++]=i;
    
    free(isprime);
    return;
}

void mpzredsquare(mpz_t r1,mpz_t r0,mpz_t m)  {
// (r1*m+r0)^2 mod m*m
// 2*r0*r1*m+r0*r0 mod m*m
   mpz_mul(r1,r1,r0);
   mpz_mul_2exp(r1,r1,1);
   mpz_fdiv_r(r1,r1,m);

   mpz_pow_ui(r0,r0,2);
   mpz_t temp;
   mpz_init(temp);
   mpz_fdiv_qr(temp,r0,r0,m);

   mpz_add(r1,r1,temp);
   if(mpz_cmp(r1,m)>=0)mpz_sub(r1,r1,m);
   mpz_clear(temp);
   return;
}

void mpzredspec(mpz_t n,mpz_t m)  {
// set m=n mod m*m
   mpz_pow_ui(m,m,2);
   mpz_mod(m,n,m);
   return;
}

void mpzred(mpz_t r1,mpz_t r0,mpz_t n,mpz_t m)  {
// n=s1*m+s0
// (r1*m+r0)*(s1*m+s0) % m*m
// ((r1*s0+r0*s1)*m+r0*s0 ) % m*m
    mpz_t s1,s0;
    mpz_init(s1);
    mpz_init(s0);
    
    mpz_fdiv_qr(s1,s0,n,m);

    mpz_mul(r1,r1,s0);
    mpz_addmul(r1,r0,s1);
    mpz_clear(s1);
    mpz_fdiv_r(r1,r1,m);

    mpz_mul(r0,r0,s0);
    mpz_fdiv_qr(s0,r0,r0,m);

    mpz_add(r1,r1,s0);
    if(mpz_cmp(r1,m)>=0)  mpz_sub(r1,r1,m);
    mpz_clear(s0);
    return;
}

void ff(mpz_ptr result,mpz_t m,lli n)  {
    // Computation of result=n! mod m^2
    int d,depth;
    unsigned int *isprime,Bits[32];
    lli i,j,st,c,ct,nn,p,up,L,L32,I,I2,si;
    mpz_t temp,*sp,*g,r0,r1;

    Bits[0]=1;
    for(i=1;i<32;i++)Bits[i]=2*Bits[i-1];
    depth=0;nn=n;
    while(nn>=1)  depth++,nn>>=1;
    
    si=1+(lli) sqrt(interval);
    g=(mpz_t*)(malloc)(si*sizeof(mpz_t));
    for(i=0;i<si;i++)mpz_init(g[i]);
    sp=(mpz_t*)(malloc)(si*sizeof(mpz_t));
    for(i=0;i<si;i++)mpz_init(sp[i]);
    
    mpz_init_set_ui(r0,1);
    mpz_init_set_ui(r1,0);
    for(d=depth;d>=0;d--)  {
    // n/(p-1)>=factorialp(n,p)>=2^d
    // n/(2^d)+1>=p
    up=1+(n>>d);
    mpzredsquare(r1,r0,m);
    ct=0;
    c=0;
    for(I=0;I<=up;)  {
        I2=I+sievelen;
        if(I2>up)  I2=up;
        L=I2-I;
        L=(L/32+1)*32;I2=I+L;
        L32=L/32;
        isprime=(unsigned int*)(malloc)(L32*sizeof(unsigned int));
        for(i=0;i<L32;i++)isprime[i]=0xffffffff;
        if(I==0)  {isprime[0]&=~Bits[0];isprime[0]&=~Bits[1];}
        
        for(i=0;i<primepi;i++)  {
            p=prime[i];
            if(p*p>=I2)break;
            st=((I+p-1)/p)*p;
            if(st<=p)  st=2*p;
            for(j=st-I;j<L;j+=p)isprime[j>>5]&=~Bits[j&31];
        }
        
        for(i=0;i<L;i++)
            if((isprime[i>>5]&Bits[i&31])>0)  {
               p=I+i;
               if((factorialp(n,p)>>d)&1)  {
                  longlongtompz(g[ct],p);ct++;
                  if(ct==si) {producttree(sp[c],g,0,ct-1);c++;ct=0;}
                  if(c==si)  {
                     mpz_init(temp);
                     producttree(temp,sp,0,c-1);
                     for(j=0;j<si;j++)mpz_clear(sp[j]);free(sp);
                     mpzred(r1,r0,temp,m);
                     mpz_clear(temp);
                     sp=(mpz_t*)(malloc)(si*sizeof(mpz_t));
                     for(j=0;j<si;j++)mpz_init(sp[j]);
                     ct=0;
                     c=0;
            }}}
        free(isprime);
        I+=L;
    }
    producttree(sp[c],g,0,ct-1);c++;
    mpz_init(temp);
    producttree(temp,sp,0,c-1);
    for(j=0;j<si;j++)mpz_clear(sp[j]);free(sp);
    mpzred(r1,r0,temp,m);
    mpz_clear(temp);
    sp=(mpz_t*)(malloc)(si*sizeof(mpz_t));
    for(j=0;j<si;j++)mpz_init(sp[j]);
    }
    
    for(i=0;i<si;i++)mpz_clear(sp[i]);free(sp);
    for(i=0;i<si;i++)mpz_clear(g[i]);free(g);
    
    mpz_set(result,r0);
    mpz_clear(r0);
    mpz_addmul(result,r1,m);
    mpz_clear(r1);

    return;
}

void ff2(mpz_ptr result,mpz_t m,lli num,lli n1,lli n2)  {
    // Computation of result=(n2!/n1!) mod m^2
    // m is the product of "num" numbers

    if(n1>n2){
       mpz_set_ui(result,1);
       return;
    }
    
    if(n1<1) n1=1;
    
    int d,depth,ty;
    unsigned int *isprime,Bits[32];
    lli i,j,st,c,ct,nn,p,q,up,L,L32,LL,I,I2,f2,f3,dist,si,*factor,*ext;
    mpz_t temp,*sp,*g,r0,r1;

    LL=n2-n1+1;// can be >2^32

    Bits[0]=1;
    for(i=1;i<32;i++)Bits[i]=2*Bits[i-1];
    depth=0;nn=n2-n1+64;
    while(nn>=1)  depth++,nn>>=1;
    
    si=(lli)sqrt(num);
    g=(mpz_t*)(malloc)(si*sizeof(mpz_t));
    for(i=0;i<si;i++)mpz_init(g[i]);
    sp=(mpz_t*)(malloc)(si*sizeof(mpz_t));
    for(i=0;i<si;i++)mpz_init(sp[i]);
    
    mpz_init_set_ui(r0,1);
    mpz_init_set_ui(r1,0);
    for(d=depth;d>=0;d--)  {
    // (n2-n1)/(p-1)+log(n2)/log(p)>=factorialp2(n2,p,LL)-factorialp2(n1,p,LL)>=2^d
    // p,n2<2^64 --> log(n2)/log(p)<16 for p>16
    // (n2-n1)/(p-1)+16>=2^d
    // max(16,(n2-n1)/(2^d-16)+1)>=p, for d>4
    if(d>4)  {up=1+(n2-n1)/((1LL<<d)-16);if(up<16)up=16;}
    else     up=LL;

    mpzredsquare(r1,r0,m);
    ct=0;
    c=0;
    for(I=0;I<=up;)  {
        I2=I+sievelen;
        if(I2>LL)  I2=LL+1;
        L=I2-I;
        L=(L/32+1)*32;I2=I+L;
        L32=L/32;
        isprime=(unsigned int*)(malloc)(L32*sizeof(unsigned int));
        for(i=0;i<L32;i++)isprime[i]=0xffffffff;
        if(I==0)  {isprime[0]&=~Bits[0];isprime[0]&=~Bits[1];}
        
        for(i=0;i<primepi;i++)  {
            p=prime[i];
            if(p*p>=I2)break;
            st=((I+p-1)/p)*p;
            if(st<=p)  st=2*p;
            for(j=st-I;j<L;j+=p)isprime[j>>5]&=~Bits[j&31];
        }
        
        for(i=0;i<L;i++)
            if((isprime[i>>5]&Bits[i&31])>0)  {
               p=I+i;
               if(((factorialp2(n2,p,LL)-factorialp2(n1,p,LL))>>d)&1)  {
                  longlongtompz(g[ct],p);ct++;
                  if(ct==si) {producttree(sp[c],g,0,ct-1);c++;ct=0;}
                  if(c==si)  {
                     mpz_init(temp);
                     producttree(temp,sp,0,c-1);
                     for(j=0;j<si;j++)mpz_clear(sp[j]);free(sp);
                     mpzred(r1,r0,temp,m);
                     mpz_clear(temp);
                     sp=(mpz_t*)(malloc)(si*sizeof(mpz_t));
                     for(j=0;j<si;j++)mpz_init(sp[j]);
                     ct=0;
                     c=0;
            }}}
        free(isprime);
        I+=L;
    }
    
    if(d==0)  {
    // two strategy: sieve up to sqrt(n2)
    //               sieve up to LL
    // (choose the smaller)
    if((lli)1+sqrt(n2)<LL)  ty=0,dist=1+(int)sqrt(n2);
    else                               ty=1,dist=LL;
    
    for(I=n1+1;I<=n2;)  {// n1>0
        I2=I+dist;
        if(I2>n2)  I2=n2+1;
        L=I2-I;
        factor=(lli*)(malloc)(L*sizeof(lli));
        ext=(lli*)(malloc)(L*sizeof(lli));
        for(i=0;i<L;i++)factor[i]=1;
        for(i=0;i<L;i++)ext[i]=1;
        
        for(i=0;i<primepi&&prime[i]<=dist;i++)  {
            p=prime[i];
            q=1;
            while(q<=LL/p){
                  q*=p;
                  st=((I+q-1)/q)*q;
                  for(j=st-I;j<L;j+=q)factor[j]*=p;
            }
            while(q<=n2/p){
                  q*=p;
                  st=((I+q-1)/q)*q;
                  for(j=st-I;j<L;j+=q)ext[j]*=p;
            }
        }
        
        for(i=0;i<L;i++)  {
            if(ty==1)  f2=(I+i)/factor[i];
            else  {
               f2=ext[i];
               f3=(I+i)/(f2*factor[i]);// f3 is prime or one
               if(f3>LL)f2*=f3;
            }
            if(f2>1)  {
                  longlongtompz(g[ct],f2);ct++;
                  if(ct==si) {producttree(sp[c],g,0,ct-1);c++;ct=0;}
                  if(c==si)  {
                     mpz_init(temp);
                     producttree(temp,sp,0,c-1);
                     for(j=0;j<si;j++)mpz_clear(sp[j]);free(sp);
                     mpzred(r1,r0,temp,m);
                     mpz_clear(temp);
                     sp=(mpz_t*)(malloc)(si*sizeof(mpz_t));
                     for(j=0;j<si;j++)mpz_init(sp[j]);
                     ct=0;
                     c=0;
            }}}
        I+=L;
        free(factor);
        free(ext);
    }
    }
    producttree(sp[c],g,0,ct-1);c++;
    mpz_init(temp);
    producttree(temp,sp,0,c-1);
    for(j=0;j<si;j++)mpz_clear(sp[j]);free(sp);
    mpzred(r1,r0,temp,m);
    mpz_clear(temp);
    sp=(mpz_t*)(malloc)(si*sizeof(mpz_t));
    for(j=0;j<si;j++)mpz_init(sp[j]);
    }
    
    for(i=0;i<si;i++)mpz_clear(sp[i]);free(sp);
    for(i=0;i<si;i++)mpz_clear(g[i]);free(g);
    
    mpz_set(result,r0);
    mpz_clear(r0);
    mpz_addmul(result,r1,m);
    mpz_clear(r1);

    return;
}


int main()  {

    assert(sizeof(int)>=4&&sizeof(lli)>=8);
    int done,add[3]={6,12,12},di[3]={6,4,2},d,dd,ty,*t1,*t2,*g30030,printtofile,inv;
    int info[3][2]={{1,3},{5,12},{11,12}};
    unsigned int ui,*diff;
    lli i,j,numprimes,num,ct,c,sg,si,pos,pos2,pow2,POW2,up,*tot;
    lli *firstprime,*pr,*prim,u1,u2,v,pp1,pp2,lim;
    time_t sec;
    mpz_t st,en,n,n2,p,p2,r,temp,temp2,prec,w,T,bigmult,*g,*res,*res2,*rr,*A,S[3];
    mpz_init(st);
    mpz_init(en);
    mpz_init(n);
    mpz_init(n2);
    mpz_init(p);
    mpz_init(p2);
    mpz_init(r);
    mpz_init(temp);
    mpz_init(temp2);
    mpz_init(prec);
    mpz_init(w);
    for(i=0;i<3;i++)mpz_init(S[i]);
    FILE* out;
    FILE* out2;
    
    // comment out to use wilsonremainder()
    // while(gmp_scanf("%Zd",&p)!=EOF){sec=time(NULL);wilsonremainder(r,p);gmp_printf("wilson(%Zd)=%Zd,time=%ld sec.\n",p,r,time(NULL)-sec);}

   int ans=0;
   FILE *in;
   in=fopen("wilsonwork.txt","r");
   if(in!=NULL)  {
      printf("Found unfinished work, would you like to continue it? (0/1) ");scanf("%d",&ans);
      if(ans!=0)  {
        gmp_fscanf(in,"st=%Zd-en=%Zd\n",&st,&en);
        for(i=0;i<3;i++)  gmp_fscanf(in,"S[%lld]=%Zd\n",&i,&S[i]);
        fscanf(in,"interval=%lld\n",&interval);
        fscanf(in,"printtofile=%d\n",&printtofile);
        gmp_printf("Continue the st=%Zd, en=%Zd search; process %lld primes at once; printtofile=%d.\n",st,en,interval,printtofile);
        for(i=0;i<3;i++)  gmp_printf("done p<%Zd, p==%d mod %d\n",S[i],info[i][0],info[i][1]);
        fclose(in);
     }
   }
   else printf("Not found unfinished workunit.\n");
    
    if(ans==0)  {
    printf("Please give start and end value of the search! ");gmp_scanf("%Zd %Zd",&st,&en);
    printf("Give how many primes to process at once: ");scanf("%lld",&interval);
    printf("Do you want to print to file all residues (0/1)? (Warning large text file!): ");scanf("%d",&printtofile);
    printf("All interesting residues in wilson.txt (res=-1+kp, where abs(k)<=%d)\n",bound);
    }
    sec=time(NULL);

    if(mpz_cmp_ui(st,5)<0)  mpz_set_ui(st,5);// skip p=2,3
    if(mpz_cmp(st,en)>0)  return 0;// trivial case
    
    assert(interval>0);
    assert(mpz_sizeinbase(en,2)<=61);
    
    if(ans==0)  {
    sg=1+interval/BR;
    if(sg&1)sg++;// now sg is even
    interval=sg*BR;// now interval is divisible by sg, so it is also even
    }
    else  {assert(interval%(2*BR)==0);sg=interval/BR;}

    if(printtofile)  out=fopen("wilsonres.txt","a");

    g=(mpz_t*)(malloc)(sg*sizeof(mpz_t));
    for(i=0;i<sg;i++)mpz_init(g[i]);
    A=(mpz_t*)(malloc)(BR*sizeof(mpz_t));
    for(i=0;i<BR;i++)mpz_init(A[i]);
    res2=(mpz_t*)(malloc)(sg*sizeof(mpz_t));
    for(i=0;i<sg;i++)mpz_init(res2[i]);
    tot=(lli*)(malloc)(BR*sizeof(lli));
    firstprime=(lli*)(malloc)(BR*sizeof(lli));
    pr=(lli*)(malloc)(sg*sizeof(lli));
    diff=(unsigned int*)(malloc)(interval/2*sizeof(unsigned int));
    g30030=(int*)(malloc)(30030*sizeof(int));
    
    for(i=0;i<30030;i++)g30030[i]=(i%2>0&&i%3>0&&i%5>0&&i%7>0&&i%11>0&&i%13>0);
    // to quickly eliminate composites
    // 30030=2*3*5*7*11*13

    mpz_set(n,st);
    mpz_fdiv_q_ui(temp,en,2);
    sievelen=3+(int) sqrt(mpztolonglong(temp));// we need only primes up to sqrt(en/2) for sieve
    if(sievelen<64)sievelen=64; // minimal sievelen is 64
    initprimes(sievelen);
    
    if(ans==0)  {
    i=mpz_fdiv_r_ui(temp,n,12);
    mpz_add_ui(S[0],n,(12+1-i)%6);
    mpz_add_ui(S[1],n,(12+5-i)%12);
    mpz_add_ui(S[2],n,(12+11-i)%12);
    }
    else  {
      assert(mpz_fdiv_r_ui(temp,S[0],6)==1);
      assert(mpz_fdiv_r_ui(temp,S[1],12)==5);
      assert(mpz_fdiv_r_ui(temp,S[2],12)==11);
    }

    while(1){
    
    done=0;
    for(i=0;i<3;i++)
        if(mpz_cmp(S[i],en)>0)done++;
    if(done==3)break;
    
    for(i=0;i<3;i++)
        if(i==0||mpz_cmp(S[i],n)<0){ty=i;mpz_set(n,S[i]);}

    remove("wilsonwork.txt");
    out2=fopen("wilsonwork.txt","w");    
    gmp_fprintf(out2,"st=%Zd-en=%Zd\n",st,en);
    for(i=0;i<3;i++)gmp_fprintf(out2,"S[%lld]=%Zd\n",i,S[i]);
    fprintf(out2,"interval=%lld\n",interval);
    fprintf(out2,"printtofile=%d\n",printtofile);
    fclose(out2);

    d=add[ty];
    dd=di[ty];
    c=0;
    ct=0;
    numprimes=0;
    for(i=0;i<interval/2;i++)diff[i]=0;
    for(i=0;i<BR;i++)tot[i]=0;
    while(mpz_cmp(n,en)<=0)  {
          mpz_add_ui(n2,n,d);
          if(mpz_probab_prime_p(n,reps)>0)  {
             mpz_set(g[c],n);
             if(c==0)  firstprime[ct]=mpztolonglong(n);
             else      {
                mpz_sub(temp,n,prec);
                ui=mpz_get_ui(temp);
                ui/=d;
                diff[numprimes>>1]+=ui<<(16*(numprimes&1));
             }
             tot[ct]++;
             c++;
             if(c==sg)  {producttree(A[ct],g,0,c-1);ct++;c=0;}
             numprimes++;
             mpz_set(prec,n);
          }
          
          if((ct==BR||mpz_cmp(n2,en)>0)&&numprimes>0)  {
                gmp_printf("\r\r\r\r\r\r\r\r\r\rTesting p=%lld...%Zd, p==%d mod %d, time=%ld sec.       ",firstprime[0],prec,info[ty][0],info[ty][1],time(NULL)-sec);
                fflush(stdout);
                if(c>0)  {producttree(A[ct],g,0,c-1);ct++;c=0;}
                
                mpz_init(bigmult);
                producttree(bigmult,A,0,ct-1);
                
                mpz_init(T);
                ff(T,bigmult,(firstprime[0]-1)/dd);
                mpz_clear(bigmult);
                res=(mpz_t*)(malloc)(ct*sizeof(mpz_t));
                for(i=0;i<ct;i++)mpz_init_set_ui(res[i],1);
                remaindertree(T,A,res,0,ct-1);
                mpz_clear(T);
                
                if(1)func((firstprime[0]-1)/dd+1,(mpztolonglong(prec)-1)/dd+1,A,res,firstprime,dd,0,ct-1,2);
                else {//another strategy, it seems slower
                mpz_init(T);
                for(i=0;i+1<ct;i++)  {
                producttree2(T,(firstprime[i]-1)/dd+1,(firstprime[i+1]-1)/dd);
                for(j=i+1;j<ct;j++)  {
                    mpz_mul(temp,T,res[j]);
                    mpz_pow_ui(r,A[j],2);
                    mpz_mod(res[j],temp,r);
                }}
                mpz_clear(T);
                mpz_clear(r);
                mpz_init(r);}
                
                for(i=0;i<BR;i++)mpz_clear(A[i]);free(A);
                
                si=interval/BR+sg;
                rr=(mpz_t*)(malloc)(si*sizeof(mpz_t));
                for(i=0;i<si;i++)mpz_init(rr[i]);
                prim=(lli*)(malloc)(si*sizeof(lli));
                t1=(int*)(malloc)(si*sizeof(int));
                t2=(int*)(malloc)(si*sizeof(int));
                
                num=0;
                for(i=0;i<ct;i++)  {
                    numprimes=tot[i];
                    longlongtompz(g[0],firstprime[i]);
                    for(j=1;j<numprimes;j++)mpz_add_ui(g[j],g[j-1],d*((diff[(sg*i+j)>>1]>>(16*(j&1)))&65535));
                    for(j=0;j<numprimes;j++)pr[j]=mpztolonglong(g[j]);
                    
                    for(j=0;j<numprimes;j++)mpz_set_ui(res2[j],1);
                    func((pr[0]-1)/dd+1,(pr[numprimes-1]-1)/dd+1,g,res2,pr,dd,0,numprimes-1,6);
                    remaindertree2(res[i],g,res2,0,numprimes-1);
                    
                    for(j=0;j<numprimes;j++){
                        mpz_set(rr[num],res2[j]);
                        prim[num]=pr[j];
                        num++;
                    }
                    
                    if(i==ct-1||num>=interval/BR)  {
                       POW2=1;
                       while(POW2<=num/2)POW2<<=1;
                       switch(ty)  {
                               case 0:
                                   pp1=prim[0];
                                   pp2=prim[num-1];
                                   
                                   up=(int)sqrt(4*pp2/27);
                                   lim=(int)sqrt(4*pp2);
                                   for(u1=0;u1<=up;u1++)  {
                                       while(27*u1*u1+lim*lim>4*pp2)lim--;
                                       for(u2=lim;27*u1*u1+u2*u2>=4*pp1&&u2>=0;u2--)  {
                                           if(u2%3>0){
                                           v=27*u1*u1+u2*u2;
                                           if((v&3)==0&&(v<=52||g30030[(v>>2)%30030])){
                                           pos=0;
                                           pow2=POW2;
                                           while(pow2){
                                                 pos2=pos+pow2;
                                                 if(pos2<num&&4*prim[pos2]<=v)pos=pos2;
                                                 pow2>>=1;
                                           }
                                           if(4*prim[pos]==v)t1[pos]=u2;
                                           }}
                                      }
                                  }
                                  
                                   up=(int)sqrt(4*pp2/3);
                                   lim=(int)sqrt(4*pp2);
                                   for(u1=0;u1<=up;u1++)  {
                                       while(3*u1*u1+lim*lim>4*pp2)lim--;
                                       for(u2=lim;3*u1*u1+u2*u2>=4*pp1&&u2>=0;u2--)  
                                           if(u2%3>0)  {
                                           v=3*u1*u1+u2*u2;
                                           if((v&3)==0&&(v<=52||g30030[(v>>2)%30030])){
                                           pos=0;
                                           pow2=POW2;
                                           while(pow2){
                                                 pos2=pos+pow2;
                                                 if(pos2<num&&4*prim[pos2]<=v)pos=pos2;
                                                 pow2>>=1;
                                           }
                                           if(4*prim[pos]==v)t2[pos]=u2;}
                                      }
                                  }

                                  for(j=0;j<num;j++)  {
                                      longlongtompz(p,prim[j]);
                                      mpz_pow_ui(p2,p,2);
                                      
                                      mpz_powm_ui(r,rr[j],6,p2);
                                      //c=t1[j];u=t2[j], actually c=+-t1[j];u=+-t2[j] we'll negate at the end
                                      mpz_set_ui(temp,2);
                                      mpz_powm(temp,temp,p,p2);
                                      mpz_sub_ui(temp,temp,1);
                                      mpz_neg(temp,temp);
                                      mpz_ui_pow_ui(temp2,t2[j],3);
                                      mpz_mul(temp,temp,temp2);
                                      mpz_mul_ui(temp2,p,t2[j]);
                                      mpz_mul_ui(temp2,temp2,3);
                                      mpz_add(temp,temp,temp2);
                                      mpz_mul(r,r,temp);
                                      
                                      mpz_set_ui(temp,t1[j]);
                                      mpz_invert(temp,temp,p2);
                                      mpz_mul(temp,temp,p);
                                      mpz_sub_ui(temp,temp,t1[j]);
                                      mpz_mul(r,r,temp);
                                      
                                      mpz_set_ui(temp,3);
                                      mpz_powm(temp,temp,p,p2);
                                      mpz_sub_ui(temp,temp,1);
                                      if(mpz_odd_p(temp)!=0)  mpz_add(temp,temp,p2);
                                      mpz_divexact_ui(temp,temp,2);
                                      mpz_mul(r,r,temp);
                                      
                                      inv=0;
                                      if(t1[j]%3==2)inv=1-inv;
                                      // (-1)^n=1-2*(n&1)
                                      if((3+t2[j]-1+2*(((prim[j]-1)/6)&1))%3>0)inv=1-inv;
                                      if(inv)mpz_neg(r,r);
                                      
                                      mpz_mod(rr[j],r,p2);
                                  }
                                  break;
                               case 1:
                                   pp1=prim[0];
                                   pp2=prim[num-1];
                                   
                                   up=(int)sqrt(pp2);
                                   lim=up;
                                   if(lim&1)lim--;
                                   for(u1=1;u1<=up;u1+=2)  {
                                       while(u1*u1+lim*lim>pp2)lim-=2;
                                       for(u2=lim;u1*u1+u2*u2>=pp1&&u2>=0;u2-=2)  {
                                           v=u1*u1+u2*u2;
                                           if(v<=13||g30030[v%30030]){
                                           pos=0;
                                           pow2=POW2;
                                           while(pow2){
                                                 pos2=pos+pow2;
                                                 if(pos2<num&&prim[pos2]<=v)pos=pos2;
                                                 pow2>>=1;
                                           }
                                           if(prim[pos]==v)t1[pos]=u1;}
                                      }
                                  }

                                  for(j=0;j<num;j++)  {
                                      longlongtompz(p,prim[j]);
                                      mpz_pow_ui(p2,p,2);
                                      
                                      mpz_powm_ui(r,rr[j],4,p2);
                                      //a=t1[j]
                                      mpz_set_ui(temp,2);
                                      mpz_powm(temp,temp,p,p2);
                                      mpz_mul_ui(temp,temp,3);
                                      mpz_sub_ui(temp,temp,4);
                                      mpz_mul(r,r,temp);
                                      
                                      mpz_set_ui(temp,t1[j]);
                                      mpz_pow_ui(temp,temp,2);
                                      mpz_mul_ui(temp,temp,2);
                                      mpz_sub(temp,temp,p);
                                      mpz_mul(r,r,temp);
                                      
                                      mpz_mod(rr[j],r,p2);
                                 }
                                 break;
                               case 2:
                                  for(j=0;j<num;j++)  {
                                      longlongtompz(p,prim[j]);
                                      mpz_pow_ui(p2,p,2);
                                      
                                      mpz_powm_ui(r,rr[j],2,p2);
                                      
                                      mpz_set_ui(temp,2);
                                      mpz_powm(temp,temp,p,p2);
                                      mpz_sub_ui(temp,temp,1);
                                      mpz_neg(temp,temp);
                                      mpz_mul(r,r,temp);

                                      mpz_mod(rr[j],r,p2);
                                 }
                                 break;

                               default:break;
                       }
                       for(j=0;j<num;j++)  {
                           longlongtompz(p,prim[j]);
                           mpz_pow_ui(p2,p,2);
                           mpz_set(r,rr[j]);
                           
                           if(printtofile)gmp_fprintf(out,"%Zd %Zd\n",p,r);
                           
                           mpz_add_ui(r,r,1);
                           mpz_fdiv_q(r,r,p);// We would use Wilson's theorem in general, but here pr[i] can be composite also.
                           if(mpz_cmp(r,p)>=0)mpz_sub(r,r,p);
                           if(mpz_cmp_ui(r,bound)>0)mpz_sub(r,r,p);
                           if(mpz_cmpabs_ui(r,bound)<=0)  {// interesting result
                             out2=fopen("wilson.txt","a+");
                             gmp_fprintf(out2,"%Zd -1",p);
                             if(mpz_sgn(r)>=0)  fprintf(out2,"+");
                             else               fprintf(out2,"-");
                             mpz_abs(r,r);
                             gmp_fprintf(out2,"%Zdp\n",r);
                             fclose(out2);}
                      }
                      num=0;
                    }
               }
                       
               si=interval/BR+sg;
               for(j=0;j<si;j++)mpz_clear(rr[j]);free(rr);
               free(prim);
               free(t1);
               free(t2);
               for(j=0;j<ct;j++)mpz_clear(res[j]);free(res);
               A=(mpz_t*)(malloc)(BR*sizeof(mpz_t));
               for(i=0;i<BR;i++)mpz_init(A[i]);
               c=0;
               ct=0;
               numprimes=0;
               mpz_set(n,n2);
               break;
               }
               mpz_set(n,n2);
            }
            mpz_set(S[ty],n);
         }
   
   gmp_printf("\r\r\r\r\r\r\r\r\r\rDone the st=%Zd-en=%Zd interval. Time=%ld sec.                                             \n",st,en,time(NULL)-sec);
   if(printtofile)  fclose(out);
   remove("wilsonwork.txt");
   
   for(i=0;i<BR;i++)mpz_clear(A[i]);free(A);
   for(i=0;i<sg;i++)mpz_clear(res2[i]);free(res2);
   for(i=0;i<sg;i++)mpz_clear(g[i]);free(g);
   for(i=0;i<3;i++)mpz_clear(S[i]);
   mpz_clear(st);
   mpz_clear(en);
   mpz_clear(n);
   mpz_clear(n2);
   mpz_clear(p);
   mpz_clear(p2);
   mpz_clear(r);
   mpz_clear(temp);
   mpz_clear(temp2);
   mpz_clear(prec);
   mpz_clear(w);
   free(pr);
   free(diff);
   free(firstprime);
   free(tot);
   free(g30030);
   free(prime);

   return 0;
}
