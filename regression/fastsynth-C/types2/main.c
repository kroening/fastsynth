int EXPRESSION(unsigned char);
unsigned char nondet_unsigned_char();

int main()
{
  unsigned char in=nondet_unsigned_char();
  int out;
  out=EXPRESSION(in);
  // the below needs promotion, or overflows
  __CPROVER_assert(out==in+in, "");
  return 0;
}
