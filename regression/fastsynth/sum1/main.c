int EXPRESSION(int, int);
int nondet_int();

int main()
{
  int in=nondet_int(), out;
  out=EXPRESSION(in, 0);
  __CPROVER_assert(out==in+in, "");

  return 0;
}
