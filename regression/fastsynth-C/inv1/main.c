__CPROVER_bool EXPRESSION_inv(unsigned);

int main()
{
  unsigned x;

  // base case  
  x=0;
  __CPROVER_assert(EXPRESSION_inv(x), "base case");

  // step case
  __CPROVER_havoc_object(&x);

  // assume the invariant holds
  if(EXPRESSION_inv(x))
  {
    // do the transition
    x++;

    if(x!=1000)
    {
      // check the property
      __CPROVER_assert(x!=2000, "property");

      // re-establish invariant
      __CPROVER_assert(EXPRESSION_inv(x), "step case");    
    }
  }  

  return 0;
}
