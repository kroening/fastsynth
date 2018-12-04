int EXPRESSION(void);
int nondet_int(void);

int main()
{
  int x=EXPRESSION();
  int y=nondet_int();
  __CPROVER_assume(y==20);
  __CPROVER_assert(x==y, "equality");
}
