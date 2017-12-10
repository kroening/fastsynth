int EXPRESSION_xor(int, int);

int main()
{
  int in0, in1;
  __CPROVER_assert(EXPRESSION_xor(in0, in1)==(in0 ^ in1), "");
}
