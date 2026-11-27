asm {
_HOL_INVOKE::
    PUSH RBP
    MOV RBP,RSP
    MOV RAX,U64 SF_ARG1[RBP]
    PUSH U64 SF_ARG2[RBP]
    CALL RAX
    POP RBP
    RET1 16
}

_extern _HOL_INVOKE I64 HolInvoke(I64 code,I64 *args);

#define HOL_CHUNK 0x1000000
#define HOL_SMALL 0x4000000000000000

U8 *hol_chunk=NULL;
I64 hol_used=0,hol_size=0,hol_perm=0;
U8 *hol_chunks[1024];
I64 hol_count=0;

I64 *HolAlloc(I64 words)
{
  I64 bytes=words*8,size;
  U8 *p;
  if (bytes<8) bytes=8;
  if (hol_perm) return MAlloc(bytes,adam_task);
  if (hol_used+bytes>hol_size) {
    size=HOL_CHUNK;
    if (bytes>size) size=bytes;
    if (hol_count>=1024) throw('Heap');
    hol_chunk=MAlloc(size,adam_task);
    if (!hol_chunk) throw('Heap');
    hol_chunks[hol_count++]=hol_chunk;
    hol_size=size;
    hol_used=0;
  }
  p=hol_chunk+hol_used;
  hol_used+=bytes;
  return p;
}

U0 HolReset()
{
  I64 i;
  for (i=0;i<hol_count;i++) Free(hol_chunks[i]);
  hol_count=0;
  hol_chunk=NULL;
  hol_used=0;
  hol_size=0;
  hol_perm=0;
}

U0 HolPermOn()
{
  hol_perm++;
}

U0 HolPermOff()
{
  hol_perm--;
}

I64 HolCon(...)
{
  I64 *o=HolAlloc(argc),i;
  for (i=0;i<argc;i++) o[i]=argv[i];
  return o;
}

I64 HolRec(I64 n)
{
  return HolAlloc(n);
}

U0 HolSet(I64 *o,I64 i,I64 v)
{
  o[i]=v;
}

I64 HolF(I64 *o,I64 i)
{
  return o[i];
}

I64 HolTag(I64 x)
{
  I64 *p;
  if (x(U64)<4096) return x;
  p=x;
  return p[0];
}

I64 HolClo(...)
{
  I64 *o=HolAlloc(argc+1),i;
  o[0]=argv[0];
  o[1]=argv[1];
  o[2]=argc-2;
  for (i=2;i<argc;i++) o[i+1]=argv[i];
  return o;
}

I64 HolAp(I64 *f,I64 x)
{
  I64 n=f[2],i,*o=HolAlloc(n+4);
  o[0]=f[0];
  o[1]=f[1];
  o[2]=n+1;
  for (i=0;i<n;i++) o[i+3]=f[i+3];
  o[n+3]=x;
  if (n+1==f[1]) return HolInvoke(f[0],o+3);
  return o;
}

I64 HbNot(I64 a)
{
  return !a;
}

I64 HbAnd(I64 a,I64 b)
{
  return a && b;
}

I64 HbOr(I64 a,I64 b)
{
  return a || b;
}

I64 HbImp(I64 a,I64 b)
{
  return !a || b;
}

I64 HiOfI64(I64 v)
{
  I64 *p;
  U64 m;
  if (v>=-HOL_SMALL && v<HOL_SMALL) return v<<1|1;
  if (v<0) m=-v;
  else m=v;
  if (m>>32) {
    p=HolAlloc(3);
    p[0]=2;
    p[1]=m&0xFFFFFFFF;
    p[2]=m>>32;
  } else {
    p=HolAlloc(2);
    p[0]=1;
    p[1]=m;
  }
  if (v<0) p[0]=-p[0];
  return p;
}

I64 HiLen(I64 x)
{
  I64 *p;
  if (x&1) return 2;
  p=x;
  if (p[0]<0) return -p[0];
  return p[0];
}

I64 HiUnpack(I64 x,I64 *mag,I64 *sign)
{
  I64 *p,n,i,v;
  U64 m;
  if (x&1) {
    v=x>>1;
    if (v<0) {
      *sign=-1;
      m=-v;
    } else {
      *sign=1;
      m=v;
    }
    if (!m) {
      *sign=0;
      return 0;
    }
    mag[0]=m&0xFFFFFFFF;
    mag[1]=m>>32;
    if (mag[1]) return 2;
    return 1;
  }
  p=x;
  n=p[0];
  if (n<0) {
    *sign=-1;
    n=-n;
  } else *sign=1;
  for (i=0;i<n;i++) mag[i]=p[i+1];
  return n;
}

I64 HiMake(I64 sign,I64 *mag,I64 n)
{
  I64 *p,i;
  U64 m;
  while (n>0 && !mag[n-1]) n--;
  if (!n || !sign) return 1;
  if (n<=2) {
    m=mag[0];
    if (n==2) m|=mag[1]<<32;
    if (m<HOL_SMALL) {
      if (sign<0) return HiOfI64(-m);
      return HiOfI64(m);
    }
    if (sign<0 && m==HOL_SMALL) return HiOfI64(-HOL_SMALL);
  }
  p=HolAlloc(n+1);
  p[0]=sign*n;
  for (i=0;i<n;i++) p[i+1]=mag[i];
  return p;
}

I64 MagCmp(I64 *a,I64 la,I64 *b,I64 lb)
{
  I64 i;
  if (la!=lb) {
    if (la<lb) return -1;
    return 1;
  }
  for (i=la-1;i>=0;i--) {
    if (a[i](U64)<b[i](U64)) return -1;
    if (a[i](U64)>b[i](U64)) return 1;
  }
  return 0;
}

I64 MagAdd(I64 *a,I64 la,I64 *b,I64 lb,I64 *r)
{
  I64 i,n=la;
  U64 c=0,t;
  if (lb>n) n=lb;
  for (i=0;i<n;i++) {
    t=c;
    if (i<la) t+=a[i](U64);
    if (i<lb) t+=b[i](U64);
    r[i]=t&0xFFFFFFFF;
    c=t>>32;
  }
  r[n]=c;
  return n+1;
}

I64 MagSub(I64 *a,I64 la,I64 *b,I64 lb,I64 *r)
{
  I64 i,t,c=0;
  for (i=0;i<la;i++) {
    t=a[i]-c;
    if (i<lb) t-=b[i];
    if (t<0) {
      t+=0x100000000;
      c=1;
    } else c=0;
    r[i]=t;
  }
  return la;
}

I64 MagMul(I64 *a,I64 la,I64 *b,I64 lb,I64 *r)
{
  I64 i,j;
  U64 c,t;
  for (i=0;i<la+lb;i++) r[i]=0;
  for (i=0;i<la;i++) {
    c=0;
    for (j=0;j<lb;j++) {
      t=r[i+j](U64)+a[i](U64)*b[j](U64)+c;
      r[i+j]=t&0xFFFFFFFF;
      c=t>>32;
    }
    r[i+lb]=c;
  }
  return la+lb;
}

U0 MagShl1(I64 *r,I64 n,I64 bit)
{
  I64 i;
  U64 c=bit,t;
  for (i=0;i<n;i++) {
    t=r[i](U64)<<1|c;
    r[i]=t&0xFFFFFFFF;
    c=t>>32;
  }
}

I64 MagTrim(I64 *a,I64 n)
{
  while (n>0 && !a[n-1]) n--;
  return n;
}

U0 MagDivMod(I64 *a,I64 la,I64 *b,I64 lb,I64 *q,I64 *r)
{
  I64 i,bit,lr;
  U64 d,cur,rem=0;
  for (i=0;i<la;i++) q[i]=0;
  if (lb==1) {
    d=b[0];
    for (i=la-1;i>=0;i--) {
      cur=rem<<32|a[i](U64);
      q[i]=cur/d;
      rem=cur%d;
    }
    r[0]=rem;
    for (i=1;i<=lb;i++) r[i]=0;
    return;
  }
  for (i=0;i<=lb;i++) r[i]=0;
  for (bit=la*32-1;bit>=0;bit--) {
    MagShl1(r,lb+1,(a[bit>>5]>>(bit&31))&1);
    lr=MagTrim(r,lb+1);
    if (MagCmp(r,lr,b,lb)>=0) {
      MagSub(r,lr,b,lb,r);
      q[bit>>5]|=1<<(bit&31);
    }
  }
}

I64 HiAdd(I64 x,I64 y)
{
  I64 *a,*b,*r,la,lb,sa,sb,c;
  if (x&y&1) return HiOfI64((x>>1)+(y>>1));
  a=HolAlloc(HiLen(x));
  b=HolAlloc(HiLen(y));
  la=HiUnpack(x,a,&sa);
  lb=HiUnpack(y,b,&sb);
  if (!sa) return y;
  if (!sb) return x;
  r=HolAlloc(la+lb+1);
  if (sa==sb) return HiMake(sa,r,MagAdd(a,la,b,lb,r));
  c=MagCmp(a,la,b,lb);
  if (!c) return 1;
  if (c>0) return HiMake(sa,r,MagSub(a,la,b,lb,r));
  return HiMake(sb,r,MagSub(b,lb,a,la,r));
}

I64 HiNeg(I64 x)
{
  I64 *p,*q,i,n;
  if (x&1) return HiOfI64(-(x>>1));
  p=x;
  n=HiLen(x);
  q=HolAlloc(n+1);
  q[0]=-p[0];
  for (i=1;i<=n;i++) q[i]=p[i];
  return q;
}

I64 HiSub(I64 x,I64 y)
{
  if (x&y&1) return HiOfI64((x>>1)-(y>>1));
  return HiAdd(x,HiNeg(y));
}

I64 HiDup(I64 x)
{
  return HiAdd(x,x);
}

I64 HiBad(I64 x,I64 y)
{
  throw('Sub');
  return x+y;
}

I64 HiSign(I64 x)
{
  I64 *p;
  if (x&1) {
    if (x>>1<0) return -1;
    if (x>>1>0) return 1;
    return 0;
  }
  p=x;
  if (p[0]<0) return -1;
  return 1;
}

I64 HiCmp(I64 x,I64 y)
{
  I64 *a,*b,la,lb,sa,sb,c;
  if (x&y&1) {
    if (x<y) return -1;
    if (x>y) return 1;
    return 0;
  }
  a=HolAlloc(HiLen(x));
  b=HolAlloc(HiLen(y));
  la=HiUnpack(x,a,&sa);
  lb=HiUnpack(y,b,&sb);
  if (sa!=sb) {
    if (sa<sb) return -1;
    return 1;
  }
  c=MagCmp(a,la,b,lb);
  if (sa<0) return -c;
  return c;
}

I64 HiEq(I64 x,I64 y)
{
  return !HiCmp(x,y);
}

I64 HiLe(I64 x,I64 y)
{
  return HiCmp(x,y)<=0;
}

I64 HiLt(I64 x,I64 y)
{
  return HiCmp(x,y)<0;
}

I64 HiAbs(I64 x)
{
  if (HiSign(x)<0) return HiNeg(x);
  return x;
}

I64 HiMul(I64 x,I64 y)
{
  I64 *a,*b,*r,la,lb,sa,sb,u,v;
  if (x&y&1) {
    u=x>>1;
    v=y>>1;
    if (u>-0x80000000 && u<0x80000000 && v>-0x80000000 && v<0x80000000) return HiOfI64(u*v);
  }
  a=HolAlloc(HiLen(x));
  b=HolAlloc(HiLen(y));
  la=HiUnpack(x,a,&sa);
  lb=HiUnpack(y,b,&sb);
  if (!sa || !sb) return 1;
  r=HolAlloc(la+lb);
  return HiMake(sa*sb,r,MagMul(a,la,b,lb,r));
}

I64 HiDivModAbs(I64 x,I64 y)
{
  I64 *a,*b,*q,*r,la,lb,sa,sb,u,v;
  if (x&y&1) {
    u=x>>1;
    v=y>>1;
    if (u<0) u=-u;
    if (v<0) v=-v;
    if (!v) return HolCon(0,1,HiOfI64(u));
    return HolCon(0,HiOfI64(u/v),HiOfI64(u%v));
  }
  a=HolAlloc(HiLen(x));
  b=HolAlloc(HiLen(y));
  la=HiUnpack(x,a,&sa);
  lb=HiUnpack(y,b,&sb);
  if (!sb) return HolCon(0,1,HiMake(1,a,la));
  if (!sa || MagCmp(a,la,b,lb)<0) return HolCon(0,1,HiMake(1,a,la));
  q=HolAlloc(la+1);
  r=HolAlloc(lb+2);
  MagDivMod(a,la,b,lb,q,r);
  return HolCon(0,HiMake(1,q,la),HiMake(1,r,lb+1));
}

U0 HiTwos(I64 sign,I64 *mag,I64 n,I64 *out,I64 size)
{
  I64 i,c=1,t;
  for (i=0;i<size;i++) {
    if (i<n) out[i]=mag[i];
    else out[i]=0;
  }
  if (sign>=0) return;
  for (i=0;i<size;i++) {
    t=(~out[i]&0xFFFFFFFF)+c;
    out[i]=t&0xFFFFFFFF;
    c=t>>32;
  }
}

I64 HiBits(I64 x,I64 y,I64 op)
{
  I64 *a,*b,*ta,*tb,*r,la,lb,sa,sb,size,i,ea,eb,e,c,t;
  if (x&y&1) {
    if (op==0) return HiOfI64((x>>1)&(y>>1));
    if (op==1) return HiOfI64((x>>1)|(y>>1));
    return HiOfI64((x>>1)^(y>>1));
  }
  a=HolAlloc(HiLen(x));
  b=HolAlloc(HiLen(y));
  la=HiUnpack(x,a,&sa);
  lb=HiUnpack(y,b,&sb);
  size=la;
  if (lb>size) size=lb;
  size++;
  ta=HolAlloc(size);
  tb=HolAlloc(size);
  r=HolAlloc(size+1);
  HiTwos(sa,a,la,ta,size);
  HiTwos(sb,b,lb,tb,size);
  ea=0;
  eb=0;
  if (sa<0) ea=0xFFFFFFFF;
  if (sb<0) eb=0xFFFFFFFF;
  for (i=0;i<size;i++) {
    if (op==0) r[i]=ta[i]&tb[i];
    else if (op==1) r[i]=ta[i]|tb[i];
    else r[i]=ta[i]^tb[i];
  }
  if (op==0) e=ea&eb;
  else if (op==1) e=ea|eb;
  else e=ea^eb;
  if (!e) return HiMake(1,r,size);
  c=1;
  for (i=0;i<size;i++) {
    t=(~r[i]&0xFFFFFFFF)+c;
    r[i]=t&0xFFFFFFFF;
    c=t>>32;
  }
  r[size]=c;
  return HiMake(-1,r,size+1);
}

I64 HiAnd(I64 x,I64 y)
{
  return HiBits(x,y,0);
}

I64 HiOr(I64 x,I64 y)
{
  return HiBits(x,y,1);
}

I64 HiXor(I64 x,I64 y)
{
  return HiBits(x,y,2);
}

I64 HiNot(I64 x)
{
  return HiSub(HiNeg(x),3);
}

I64 HiShift(I64 n)
{
  n=HiAbs(n);
  if (!(n&1)) throw('Shift');
  return n>>1;
}

I64 HiPush(I64 n,I64 x)
{
  I64 s=HiShift(n),*a,*r,la,sa,w,k,i;
  U64 t;
  a=HolAlloc(HiLen(x));
  la=HiUnpack(x,a,&sa);
  if (!sa) return 1;
  w=s>>5;
  k=s&31;
  r=HolAlloc(la+w+1);
  for (i=0;i<la+w+1;i++) r[i]=0;
  for (i=0;i<la;i++) {
    t=a[i](U64)<<k;
    r[i+w]|=t&0xFFFFFFFF;
    r[i+w+1]|=t>>32;
  }
  return HiMake(sa,r,la+w+1);
}

I64 HiDrop(I64 n,I64 x)
{
  I64 s=HiShift(n),*a,*r,la,sa,w,k,i,lr;
  U64 t;
  if (x&1) {
    if (s>62) s=62;
    return HiOfI64((x>>1)>>s);
  }
  if (HiSign(x)<0) return HiSub(HiNeg(HiDrop(n,HiSub(HiNeg(x),3))),3);
  a=HolAlloc(HiLen(x));
  la=HiUnpack(x,a,&sa);
  w=s>>5;
  k=s&31;
  if (w>=la) return 1;
  lr=la-w;
  r=HolAlloc(lr);
  for (i=0;i<lr;i++) {
    t=a[i+w](U64)>>k;
    if (i+w+1<la) t|=(a[i+w+1](U64)<<(32-k))&0xFFFFFFFF;
    r[i]=t&0xFFFFFFFF;
  }
  return HiMake(1,r,lr);
}

I64 HiBig(...)
{
  return HiMake(argv[0],argv+1,argc-1);
}

I64 HiToI64(I64 x)
{
  I64 *a,la,sa;
  U64 m;
  if (x&1) return x>>1;
  a=HolAlloc(HiLen(x));
  la=HiUnpack(x,a,&sa);
  m=a[0];
  if (la>1) m|=a[1](U64)<<32;
  if (sa<0) return -m;
  return m;
}
