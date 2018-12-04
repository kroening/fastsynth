int EXPRESSION(int);
int nondet_int();

int main()
{
  int in=nondet_int(), out;
  if(in < 0)
    goto ignore;
  out=EXPRESSION(in);
  __CPROVER_assert(out==in, "");

  ignore:
  __CPROVER_assume(0 == 1);
}
