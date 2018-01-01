int EXPRESSION(int, int, int);
int nondet_int();

int main()
{
  int in0=nondet_int(),
      in1=nondet_int(),
      in2=nondet_int(),
      out;
  out=EXPRESSION(in0, in1, in2);
  __CPROVER_assert(out==in2, "");
}
