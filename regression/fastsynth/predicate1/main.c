unsigned nondet_unsigned();

__CPROVER_bool EXPRESSION_predicate(unsigned, unsigned);

int main()
{
  unsigned int x, y;
  
  __CPROVER_assert(EXPRESSION_predicate(x, y)==(x<y), "x<y");

  return 0;
}

