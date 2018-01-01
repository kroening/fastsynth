unsigned EXPRESSION_inv();

int main()
{
  unsigned x;

  // base case  
  x=0;
  __CPROVER_assert(x<EXPRESSION_inv(), "base case");

  // this is a hint
  __CPROVER_assert(EXPRESSION_inv()<20, "hint");

  // step case
  __CPROVER_havoc_object(&x);

  // assume the invariant holds
  if(x<EXPRESSION_inv())
  {
    // do the transition
    x++;

    if(x!=10) // loop guard
    {
      // check the property
      __CPROVER_assert(x!=200, "property");

      // re-establish invariant
      __CPROVER_assert(x<EXPRESSION_inv(), "step case");    
    }
  }  

  return 0;
}
