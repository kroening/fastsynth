char EXPRESSION(char, char);
int nondet_int();

int main()
{
  char in1=nondet_int(), in2=nondet_int();

  char max=in1>in2?in1:in2;

  __CPROVER_assert(EXPRESSION(in1, in2)==max, "");

  return 0;
}
