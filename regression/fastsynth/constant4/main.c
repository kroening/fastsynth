int EXPRESSIONa(void);
int EXPRESSIONb(void);

int main()
{
  int asd_a, asd_b;
  asd_a=EXPRESSIONa();
  __CPROVER_assert(asd_a&1, "");

  asd_b=EXPRESSIONb();
  __CPROVER_assert(asd_a==asd_b, "");
}
