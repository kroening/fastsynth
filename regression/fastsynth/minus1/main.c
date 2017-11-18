int EXPRESSION(int);

int main()
{
  int in, out;
  out=EXPRESSION(in);
  __CPROVER_assert(out==in-20, "");
}
