int EXPRESSION(void);

int main()
{
  int asd;
  asd=EXPRESSION();
  __CPROVER_assert(asd==1, "");
  __CPROVER_assert(0, "");
}
