unsigned short EXPRESSION(unsigned char);

int main()
{
  unsigned char in;
  unsigned short out;
  out=EXPRESSION(in);
  // the below needs conversion
  __CPROVER_assert(out==in, "");
  return 0;
}
