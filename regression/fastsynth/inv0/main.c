unsigned EXPRESSION_inv();

int main()
{
  unsigned x;

  // base case  
  x=0;
  __CPROVER_assert(x<EXPRESSION_inv(), "base case");

  // step case
  __CPROVER_havoc_object(&x);

  // assume the invariant holds
  if(x<EXPRESSION_inv())
  {
    // do the transition
    x++;

    if(x!=1000)
    {
      // check the property
      __CPROVER_assert(x!=2000, "property");

      // re-establish invariant
      __CPROVER_assert(x<EXPRESSION_inv(), "step case");    
    }
  }  

  return 0;
}
