int EXPRESSION(unsigned char);

int main()
{
  unsigned char in;
  int out;
  out=EXPRESSION(in);
  // the below needs promotion, or overflows
  __CPROVER_assert(out==in+in, "");
  return 0;
}
