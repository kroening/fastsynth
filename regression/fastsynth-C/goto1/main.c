int EXPRESSION(int);
int nondet_int(void);

int main()
{
  int in=nondet_int();
  if(in < 0)
    goto ignore;

  int out=EXPRESSION(in);
  __CPROVER_assert(out==in, "");

  ignore:
  __CPROVER_assume(0 == 1);
}
