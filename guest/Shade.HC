#include "Remy.HC"
#include "Hol.HC"
#include "Holy.HC"

U8 *shade_source=NULL,*shade_code=NULL,*shade_report=NULL;
I64 shade_done=0,shade_ok=0,shade_size=0;

I64 HolList(U8 *s,I64 n)
{
  I64 l=h_empty(),i;
  for (i=n-1;i>=0;i--) l=h_cell(HiOfI64(s[i]),l);
  return l;
}

U8 *HolBytes(I64 l,I64 *size)
{
  I64 n=0,m=l,i=0;
  U8 *out;
  while (!h_finished(m)) {
    n++;
    m=h_rest(m);
  }
  out=MAlloc(n+1,adam_task);
  while (!h_finished(l)) {
    out[i++]=HiToI64(h_first(l));
    l=h_rest(l);
  }
  out[n]=0;
  if (size) *size=n;
  return out;
}

U0 Translator(U8 *rows)
{
  I64 r;
  try {
    HolReset;
    if (rows) {
      r=h_tables(HolList(shade_source,StrLen(shade_source)));
      shade_ok=h_accepted(r);
      shade_code=HolBytes(h_rows(r),&shade_size);
      shade_report=StrNew("",adam_task);
    } else {
      r=h_compile(HolList(shade_source,StrLen(shade_source)));
      shade_ok=h_status(r);
      shade_code=HolBytes(h_bytes(r),&shade_size);
      shade_report=HolBytes(h_report(r),NULL);
    }
  } catch {
    shade_ok=-1;
    shade_report=StrNew("HolyC runtime exception\n",adam_task);
    Fs->catch_except=TRUE;
  }
  HolReset;
  shade_done=1;
}

Bool Translate(U8 *source,Bool rows=FALSE)
{
  shade_source=source;
  shade_code=NULL;
  shade_report=NULL;
  shade_done=0;
  Spawn(&Translator,rows,"holy",,,64<<20);
  while (!shade_done) Sleep(1);
  return shade_ok==1;
}

U0 Shade(U8 *source)
{
  Bool ok=Translate(source);
  "%s",shade_report;
  Free(shade_report);
  if (!ok) {
    Free(shade_code);
    return;
  }
  caption="holy";
  Show(0,FALSE,shade_code,StrNew(source));
}
