int EXPRESSION_and(int, int);

int main()
{
  int in0, in1;
  __CPROVER_assert(EXPRESSION_and(in0, in1)==(in0 & in1), "");
}
