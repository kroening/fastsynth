int EXPRESSION(int);
int nondet_int();

int main()
{
  int in=nondet_int(), out;
  out=EXPRESSION(in);
  __CPROVER_assert(out==in-20, "");
}
