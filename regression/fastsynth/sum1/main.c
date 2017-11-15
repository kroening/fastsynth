int EXPRESSION(int, int);

int main()
{
  int in, out;
  out=EXPRESSION(in, in);
  __CPROVER_assert(out==in+in, "");
}
