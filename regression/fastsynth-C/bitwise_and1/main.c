int EXPRESSION_and(int, int);
int nondet_int();

int main()
{
  int in0=nondet_int(),
      in1=nondet_int();
  __CPROVER_assert(EXPRESSION_and(in0, in1)==(in0 & in1), "");
}
