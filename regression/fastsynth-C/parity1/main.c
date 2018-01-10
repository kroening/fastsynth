__CPROVER_bool EXPRESSION_parity(
  __CPROVER_bool, __CPROVER_bool, __CPROVER_bool, __CPROVER_bool);
  
__CPROVER_bool nondet_bool();

int main()
{
  __CPROVER_bool a=nondet_bool(),
                 b=nondet_bool(),
                 c=nondet_bool(),
                 d=nondet_bool(), result;

  result = EXPRESSION_parity(a, b, c, d);

  __CPROVER_assert(result == (a^b^c^d), "parity");

  return 0;
}
