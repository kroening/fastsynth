unsigned short EXPRESSION(unsigned char);
unsigned char nondet_uchar();
unsigned short nondet_ushort();

int main()
{
  unsigned char in=nondet_uchar();
  unsigned short out=nondet_ushort();
  out=EXPRESSION(in);
  // the below needs conversion
  __CPROVER_assert(out==in, "");
  return 0;
}
