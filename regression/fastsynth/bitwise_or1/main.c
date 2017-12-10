int EXPRESSION_or(int, int);

int main()
{
  int in0, in1;
  __CPROVER_assert(EXPRESSION_or(in0, in1)==(in0 | in1), "");
}
