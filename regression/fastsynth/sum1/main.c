int EXPRESSION(int, int);

int main()
{
  int in, out;
  out=EXPRESSION(in, 0);
  __CPROVER_assert(out==in+in, "");
}
