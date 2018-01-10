int EXPRESSION(void);

int main()
{
  int x=EXPRESSION();
  int y;
  __CPROVER_assume(y==20);
  __CPROVER_assert(x==y, "equality");
}
