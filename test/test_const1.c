int EXPRESSIONa(void);
int EXPRESSIONb(void);

int main()
{
  int asd;
  asd=EXPRESSIONa();
  __CPROVER_assert(asd==1, "");

  asd=EXPRESSIONb();
  if(asd!=2)
    __CPROVER_assert(0, "");
}
