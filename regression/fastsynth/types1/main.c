int EXPRESSION(short);

int main()
{
  short in;
  int out;
  out=EXPRESSION(in);
  // the below needs promotion
  __CPROVER_assert(out==in+in, "");
}
