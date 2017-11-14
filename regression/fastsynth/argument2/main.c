int EXPRESSION(int, int, int);

int main()
{
  int in0, in1, in2, out;
  out=EXPRESSION(in0, in1, in2);
  __CPROVER_assert(out==in2, "");
}
