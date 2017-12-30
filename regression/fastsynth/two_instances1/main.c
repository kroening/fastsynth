int EXPRESSION(int);

int main()
{
  int in;
  __CPROVER_assert(EXPRESSION(in)==in+1, "f(in)=in+1");
  __CPROVER_assert(EXPRESSION(in+1)==in+2, "f(in+1)==in+2");
}
