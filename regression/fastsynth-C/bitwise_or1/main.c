int EXPRESSION_or(int, int);
int nondet_int();

int main()
{
  int in0=nondet_int(),
      in1=nondet_int();
  __CPROVER_assert(EXPRESSION_or(in0, in1)==(in0 | in1), "");
}
