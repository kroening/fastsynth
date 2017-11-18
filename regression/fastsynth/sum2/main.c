int EXPRESSION(int, int);

int main()
{
  int in0, in1, out;
  out=EXPRESSION(in0, in1);
  __CPROVER_assert(out==in0+in1, "");
}
