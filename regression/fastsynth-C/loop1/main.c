int EXPRESSION(void);

int main(void)
{
  int x;
  
  for(int i=0; i<3; i++)
  {
    x=EXPRESSION();
    __CPROVER_assert(x==10, "");
  }
}
