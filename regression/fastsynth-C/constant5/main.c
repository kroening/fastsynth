int EXPRESSION(void);
int nondet_int();

int main()
{
  int x=nondet_int();

  if(x>=901)
    __CPROVER_assert(EXPRESSION()<x, "<901");
  else if(x<=900)
    __CPROVER_assert(EXPRESSION()>=x, ">=900");

  return 0;
}
