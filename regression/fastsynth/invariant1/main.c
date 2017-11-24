unsigned nondet_unsigned();

_Bool EXPRESSION_invariant(unsigned x);

int main()
{
  unsigned int x = 0u;
  
  // base case
  __CPROVER_assert(EXPRESSION_invariant(x), "base case");

#if 0  
  // step case: havoc
  x=nondet_unsigned();
  __CPROVER_assume(EXPRESSION_invariant(x));
  
  // step case: body
  x += 2u;

  // step case: check
  __CPROVER_assert(EXPRESSION_invariant(x), "step case");
  
  // property
  x=nondet_unsigned();
  __CPROVER_assume(EXPRESSION_invariant(x));
  if(x >= 0x0fffffffu) // loop exit
    __CPROVER_assert(!(x % 2u), "property");
#endif

  return 0;
}

