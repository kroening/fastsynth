int EXPRESSION(void);

int main()
{
  int x;

  if(x>=901)
    __CPROVER_assert(EXPRESSION()<x, "<901");
  else if(x<=900)
    __CPROVER_assert(EXPRESSION()>=x, ">=900");
}
