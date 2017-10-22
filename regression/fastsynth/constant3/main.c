int EXPRESSION(void);

int main()
{
  int asd;
  asd=EXPRESSION();
  __CPROVER_assert(asd==1, "");

  // there is no constant that satisfies the below
  __CPROVER_assert(0, "");
}
