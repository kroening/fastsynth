unsigned nondet_unsigned();

__CPROVER_bool EXPRESSION_predicate(unsigned, unsigned);

int main()
{
  unsigned int x=nondet_unsigned(),
               y=nondet_unsigned();
  
  __CPROVER_assert(EXPRESSION_predicate(x, y)==(x<y), "x<y");

  return 0;
}

