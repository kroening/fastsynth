int EXPRESSION(int, int);
int nondet_int();

int main()
{
  int in0=nondet_int(), in1=nondet_int(), out;
  out=EXPRESSION(in0, in1);
  __CPROVER_assert(out==in0+in1, "");
}
